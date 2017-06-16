//           layeredqbf.cc
//  Wed February 17 17:09:56 2016
//  Copyright  2016  Shahab Tasharrofi
//  <shahab.tasharrofi@gmail.com>
// layeredqbf.cc
//
// Copyright (C) 2016 - Shahab Tasharrofi
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <http://www.gnu.org/licenses/>.

#include <assert.h>
#include <unordered_set>

#include "layeredqbf.h"

bool opt_optimize_defs = false;

typedef unordered_map<Variable, Variable, Variable::hash> VarDicType;

struct PropTranslator
{
	// contains quantified variables
	unordered_set<Variable, Variable::hash> quantifiedVariables;

	// positiveInputVariables[v]=u means that v is the original name of an external
	// variable that only appears positively and is now renamed to u
	VarDicType positiveInputVariables;

	// negativeInputVariables[v]=u means that v is the original name of an external
	// variable that only appears negatively and is now renamed to u
	VarDicType negativeInputVariables;

	// nonInputVariables[v]=u means that v is the original name of an internal
	// variable that is now renamed to u
	VarDicType nonInputVariables;

	int nextAvailableVarNumber = 1;

	Variable findVar(VarDicType &dic, Variable var);

	inline void addQuantifiedVariable(Variable v) { quantifiedVariables.insert(v); }
	inline bool isQuantified(Variable v) { return quantifiedVariables.count(v) > 0; }
	inline int getTotalVarCount() { return nextAvailableVarNumber - 1; }

	Lit translate(Lit p);
};

struct ModuleTranslator
{
	// contains quantified variables
	unordered_set<Variable, Variable::hash> quantifiedVariables;

	// inputVariables[v]=u means that v is the original name of an external
	// variable which is now renamed to u
	VarDicType inputVariables;

	// nonInputVariables[v]=u means that v is the original name of an internal
	// variable that is now renamed to u
	VarDicType nonInputVariables;

	int nextAvailableVarNumber = 1;

	Variable findVar(VarDicType &dic, Variable var);

	inline void addQuantifiedVariable(Variable v) { quantifiedVariables.insert(v); }
	inline bool isQuantified(Variable v) { return quantifiedVariables.count(v) > 0; }
	inline int getTotalVarCount() { return nextAvailableVarNumber - 1; }

	inline Variable translate(Variable v) { return findVar(isQuantified(v) ? nonInputVariables : inputVariables, v); }
	inline Lit translate(Lit p) { return Lit::makeLiteral(translate(p.var), p.sign); }
};

Variable PropTranslator::findVar(VarDicType &dic, Variable var)
{
	auto it = dic.find(var);
	if (it != dic.end())
		return it->second;

	Variable result = Variable::makeVariable(nextAvailableVarNumber);
	dic[var] = result;
	nextAvailableVarNumber++;

	return result;
}

Lit PropTranslator::translate(Lit p)
{
	if (isQuantified(p.var))
		return Lit::makeLiteral(findVar(nonInputVariables, p.var), p.sign);
	else if (p.sign == SGN_POS)
		return Lit::makeLiteral(findVar(positiveInputVariables, p.var), SGN_POS);
	else
		return Lit::makeLiteral(findVar(negativeInputVariables, p.var), SGN_NEG);
}

Variable ModuleTranslator::findVar(VarDicType &dic, Variable var)
{
	auto it = dic.find(var);
	if (it != dic.end())
		return it->second;

	Variable result = Variable::makeVariable(nextAvailableVarNumber);
	dic[var] = result;
	nextAvailableVarNumber++;

	return result;
}

STSPropagatorModule *LayeredQBFProgram::convertToSTSProp(int &nextAvailableModuleNo)
{
	PropTranslator tr;
	for (int i = 0; i < quantifiedVariables.size(); i++)
		tr.addQuantifiedVariable(quantifiedVariables[i]);
	for (int i = 0; i < definitions.size(); i++)
		tr.addQuantifiedVariable(definitions[i]->outputLiteral.var);

	STSPropagatorModule *module = new STSPropagatorModule();

	if (innerLayer != NULL)
	{
		STSPropagatorModule *submodule = innerLayer->convertToSTSProp(nextAvailableModuleNo);

		NegativePropagatorSubmodule *negativeSubmodule = new NegativePropagatorSubmodule();
		negativeSubmodule->submodule = submodule;

		for (int i = 0; i < submodule->positiveInputVariables.size(); i++)
		{
			Variable currentVar = submodule->positiveInputVariables[i];
			Variable originalVar = submodule->positiveDictionary[currentVar];
			negativeSubmodule->positiveBindings.push_back(tr.translate(Lit::makeLiteral(originalVar, SGN_NEG)).var);
		}

		for (int i = 0; i < submodule->negativeInputVariables.size(); i++)
		{
			Variable currentVar = submodule->negativeInputVariables[i];
			Variable originalVar = submodule->negativeDictionary[currentVar];
			negativeSubmodule->negativeBindings.push_back(tr.translate(Lit::makeLiteral(originalVar, SGN_POS)).var);
		}

		module->negativeSubmodules.push_back(negativeSubmodule);
	}

	module->moduleNo = nextAvailableModuleNo;
	nextAvailableModuleNo++;

	unordered_set<Variable, Variable::hash> positivelyUsedVars;
	unordered_set<Variable, Variable::hash> negativelyUsedVars;

	if (opt_optimize_defs)
	{
		for (int i = 0; i < module->negativeSubmodules.size(); i++)
		{
			STSPropagatorModule *submodule = module->negativeSubmodules[i]->submodule;
			for (auto it = submodule->positiveInputVariables.cbegin(); it != submodule->positiveInputVariables.cend(); it++)
				negativelyUsedVars.insert(submodule->positiveDictionary[*it]);
			for (auto it = submodule->negativeInputVariables.cbegin(); it != submodule->negativeInputVariables.cend(); it++)
				positivelyUsedVars.insert(submodule->negativeDictionary[*it]);
		}

		for (auto it = clauses.cbegin(); it != clauses.cend(); it++)
			for (auto jt = (*it)->cbegin(); jt != (*it)->cend(); jt++)
				if ((jt->sign == SGN_NEG) ^ (qType == Q_UNIVERSAL))
				{
					if (negativelyUsedVars.count(jt->var) == 0)
						negativelyUsedVars.insert(jt->var);
				}
				else if (positivelyUsedVars.count(jt->var) == 0)
					positivelyUsedVars.insert(jt->var);

		while (true)
		{
			bool changed = false;
			for (vector<Definition *>::const_reverse_iterator it = definitions.rbegin(); it != definitions.rend(); it++)
			{
				if (positivelyUsedVars.count((*it)->outputLiteral.var) > 0)
					for (auto jt = (*it)->inputLiterals.cbegin(); jt != (*it)->inputLiterals.cend(); jt++)
					{
						if (jt->sign != (*it)->outputLiteral.sign)
						{
							if (positivelyUsedVars.count(jt->var) == 0)
							{
								positivelyUsedVars.insert(jt->var);
								changed = true;
							}
						}
						else if (negativelyUsedVars.count(jt->var) == 0)
						{
							negativelyUsedVars.insert(jt->var);
							changed = true;
						}
					}

				if (negativelyUsedVars.count((*it)->outputLiteral.var) > 0)
					for (auto jt = (*it)->inputLiterals.cbegin(); jt != (*it)->inputLiterals.cend(); jt++)
					{
						if (jt->sign != (*it)->outputLiteral.sign)
						{
							if (negativelyUsedVars.count(jt->var) == 0)
							{
								negativelyUsedVars.insert(jt->var);
								changed = true;
							}
						}
						else if (positivelyUsedVars.count(jt->var) == 0)
						{
							positivelyUsedVars.insert(jt->var);
							changed = true;
						}
					}
			}

			if (!changed)
				break;
		}
	}

	for (int i = 0; i < definitions.size(); i++)
	{
		Definition *def = definitions[i];

		Clause *clause;
		if ((!opt_optimize_defs) ||
		    ((def->outputLiteral.sign == SGN_POS) && (positivelyUsedVars.count(def->outputLiteral.var) > 0)) ||
		    ((def->outputLiteral.sign == SGN_NEG) && (negativelyUsedVars.count(def->outputLiteral.var) > 0)))
		{
			clause = new Clause();
			clause->push_back(tr.translate(def->outputLiteral.negated()));
			for (int j = 0; j < def->inputLiterals.size(); j++)
				clause->push_back(tr.translate(def->inputLiterals[j].negated()));
			module->clauses.push_back(clause);
		}

		if ((!opt_optimize_defs) ||
		    ((def->outputLiteral.sign == SGN_NEG) && (positivelyUsedVars.count(def->outputLiteral.var) > 0)) ||
		    ((def->outputLiteral.sign == SGN_POS) && (negativelyUsedVars.count(def->outputLiteral.var) > 0)))
		{
			for (int j = 0; j < def->inputLiterals.size(); j++)
			{
				clause = new Clause();
				clause->push_back(tr.translate(def->outputLiteral));
				clause->push_back(tr.translate(def->inputLiterals[j]));
				module->clauses.push_back(clause);
			}
		}
	}

	for (int i = 0; i < guardingClauses.size(); i++)
	{
		Clause *curClause = guardingClauses[i];
		Clause *newClause = new Clause();
		for (int j = 0; j < curClause->size(); j++)
			newClause->push_back(tr.translate((*curClause)[j]));
		module->clauses.push_back(newClause);
	}

	if (qType == Q_EXISTENTIAL)
	{
		for (int i = 0; i < clauses.size(); i++)
		{
			Clause *curClause = clauses[i];
			Clause *newClause = new Clause();
			for (int j = 0; j < curClause->size(); j++)
				newClause->push_back(tr.translate((*curClause)[j]));
			module->clauses.push_back(newClause);
		}
	}
	else if (clauses.size() == 1)
	{ // Universal quantifiers have at most one clause
		Clause *curClause = clauses[0];
		for (int i = 0; i < curClause->size(); i++)
		{
			Clause *unitClause = new Clause();
			unitClause->push_back(tr.translate((*curClause)[i].negated()));
			module->clauses.push_back(unitClause);
		}
	}
	else if (clauses.size() > 1)
	{
		Clause *newClause = new Clause();
		for (int i = 0; i < clauses.size(); i++)
		{
			Clause *curClause = clauses[i];
			assert(curClause->size() <= 1);

			if (curClause->size() == 1)
				newClause->push_back(tr.translate((*curClause)[0].negated()));
			else if (curClause->size() == 0)
			{ // negation of an empty clause is true which already satisfies the current clause
				newClause->clear();
				break;
			}
		}
		if (newClause->size() > 0)
			module->clauses.push_back(newClause);
		else
			delete newClause; // Clause has been already satisfied
	}

	for (auto it = tr.positiveInputVariables.cbegin(); it != tr.positiveInputVariables.cend(); it++)
	{
		module->positiveInputVariables.push_back(it->second);
		module->positiveDictionary[it->second] = it->first;
	}

	for (auto it = tr.negativeInputVariables.cbegin(); it != tr.negativeInputVariables.cend(); it++)
	{
		module->negativeInputVariables.push_back(it->second);
		module->negativeDictionary[it->second] = it->first;
	}

	for (auto it = tr.nonInputVariables.cbegin(); it != tr.nonInputVariables.cend(); it++)
		module->internalDictionary[it->second] = it->first;

	module->variableCount = max(tr.getTotalVarCount(), 1);

	return module;
}

STSModule *LayeredQBFProgram::convertToSTS(int &nextAvailableModuleNo)
{
	ModuleTranslator tr;
	for (int i = 0; i < quantifiedVariables.size(); i++)
		tr.addQuantifiedVariable(quantifiedVariables[i]);
	for (int i = 0; i < definitions.size(); i++)
		tr.addQuantifiedVariable(definitions[i]->outputLiteral.var);

	STSModule *module = new STSModule();

	if (innerLayer != NULL)
	{
		STSModule *submodule = innerLayer->convertToSTS(nextAvailableModuleNo);

		NegativeSubmodule *negativeSubmodule = new NegativeSubmodule();
		negativeSubmodule->submodule = submodule;

		for (int i = 0; i < submodule->inputVariables.size(); i++)
		{
			Variable currentVar = submodule->inputVariables[i].first;
			Variable originalVar = submodule->externalDictionary[currentVar];
			negativeSubmodule->bindings.push_back(tr.translate(originalVar));
		}

		module->negativeSubmodules.push_back(negativeSubmodule);
	}

	module->moduleNo = nextAvailableModuleNo;
	nextAvailableModuleNo++;

	unordered_set<Variable, Variable::hash> positivelyUsedVars;
	unordered_set<Variable, Variable::hash> negativelyUsedVars;

	if (opt_optimize_defs)
	{
		for (int i = 0; i < module->negativeSubmodules.size(); i++)
		{
			STSModule *submodule = module->negativeSubmodules[i]->submodule;
			for (auto it = submodule->inputVariables.cbegin(); it != submodule->inputVariables.cend(); it++)
			{
				if (it->second.first)
					negativelyUsedVars.insert(submodule->externalDictionary[it->first]);
				if (it->second.second)
					positivelyUsedVars.insert(submodule->externalDictionary[it->first]);
			}
		}

		for (auto it = clauses.cbegin(); it != clauses.cend(); it++)
			for (auto jt = (*it)->cbegin(); jt != (*it)->cend(); jt++)
				if ((jt->sign == SGN_NEG) ^ (qType == Q_UNIVERSAL))
				{
					if (negativelyUsedVars.count(jt->var) == 0)
						negativelyUsedVars.insert(jt->var);
				}
				else if (positivelyUsedVars.count(jt->var) == 0)
					positivelyUsedVars.insert(jt->var);

		bool changed = true;
		while (changed)
		{
			changed = false;
			for (vector<Definition *>::const_reverse_iterator it = definitions.rbegin(); it != definitions.rend(); it++)
			{
				if (positivelyUsedVars.count((*it)->outputLiteral.var) > 0)
					for (auto jt = (*it)->inputLiterals.cbegin(); jt != (*it)->inputLiterals.cend(); jt++)
					{
						if (jt->sign != (*it)->outputLiteral.sign)
						{
							if (positivelyUsedVars.count(jt->var) == 0)
							{
								positivelyUsedVars.insert(jt->var);
								changed = true;
							}
						}
						else if (negativelyUsedVars.count(jt->var) == 0)
						{
							negativelyUsedVars.insert(jt->var);
							changed = true;
						}
					}

				if (negativelyUsedVars.count((*it)->outputLiteral.var) > 0)
					for (auto jt = (*it)->inputLiterals.cbegin(); jt != (*it)->inputLiterals.cend(); jt++)
					{
						if (jt->sign != (*it)->outputLiteral.sign)
						{
							if (negativelyUsedVars.count(jt->var) == 0)
							{
								negativelyUsedVars.insert(jt->var);
								changed = true;
							}
						}
						else if (positivelyUsedVars.count(jt->var) == 0)
						{
							positivelyUsedVars.insert(jt->var);
							changed = true;
						}
					}
			}
		}
	}

	for (int i = 0; i < definitions.size(); i++)
	{
		Definition *def = definitions[i];

		Clause *clause;
		if ((!opt_optimize_defs) ||
		    ((def->outputLiteral.sign == SGN_POS) && (positivelyUsedVars.count(def->outputLiteral.var) > 0)) ||
		    ((def->outputLiteral.sign == SGN_NEG) && (negativelyUsedVars.count(def->outputLiteral.var) > 0)))
		{
			clause = new Clause();
			clause->push_back(tr.translate(def->outputLiteral.negated()));
			for (int j = 0; j < def->inputLiterals.size(); j++)
				clause->push_back(tr.translate(def->inputLiterals[j].negated()));
			module->clauses.push_back(clause);
		}

		if ((!opt_optimize_defs) ||
		    ((def->outputLiteral.sign == SGN_NEG) && (positivelyUsedVars.count(def->outputLiteral.var) > 0)) ||
		    ((def->outputLiteral.sign == SGN_POS) && (negativelyUsedVars.count(def->outputLiteral.var) > 0)))
		{
			for (int j = 0; j < def->inputLiterals.size(); j++)
			{
				clause = new Clause();
				clause->push_back(tr.translate(def->outputLiteral));
				clause->push_back(tr.translate(def->inputLiterals[j]));
				module->clauses.push_back(clause);
			}
		}
	}

	for (int i = 0; i < guardingClauses.size(); i++)
	{
		Clause *curClause = guardingClauses[i];
		Clause *newClause = new Clause();
		for (int j = 0; j < curClause->size(); j++)
			newClause->push_back(tr.translate((*curClause)[j]));
		module->clauses.push_back(newClause);
	}

	if (qType == Q_EXISTENTIAL)
	{
		for (int i = 0; i < clauses.size(); i++)
		{
			Clause *curClause = clauses[i];
			Clause *newClause = new Clause();
			for (int j = 0; j < curClause->size(); j++)
				newClause->push_back(tr.translate((*curClause)[j]));
			module->clauses.push_back(newClause);
		}
	}
	else if (clauses.size() == 1)
	{ // Universal quantifiers have at most one clause
		Clause *curClause = clauses[0];
		for (int i = 0; i < curClause->size(); i++)
		{
			Clause *unitClause = new Clause();
			unitClause->push_back(tr.translate((*curClause)[i].negated()));
			module->clauses.push_back(unitClause);
		}
	}
	else if (clauses.size() > 1)
	{
		Clause *newClause = new Clause();
		for (int i = 0; i < clauses.size(); i++)
		{
			Clause *curClause = clauses[i];
			assert(curClause->size() <= 1);

			if (curClause->size() == 1)
				newClause->push_back(tr.translate((*curClause)[0].negated()));
			else if (curClause->size() == 0)
			{ // negation of an empty clause is true which already satisfies the current clause
				newClause->clear();
				break;
			}
		}
		if (newClause->size() > 0)
			module->clauses.push_back(newClause);
		else
			delete newClause; // Clause has been already satisfied
	}

	for (auto it = tr.inputVariables.cbegin(); it != tr.inputVariables.cend(); it++)
	{
		bool isPosUsed = positivelyUsedVars.count(it->second) > 0;
		bool isNegUsed = negativelyUsedVars.count(it->second) > 0;
		module->inputVariables.push_back(pair<Variable, pair<bool, bool> >(it->second, pair<bool, bool>(isPosUsed, isNegUsed)));
		module->externalDictionary[it->second] = it->first;
	}

	for (auto it = tr.nonInputVariables.cbegin(); it != tr.nonInputVariables.cend(); it++)
		module->internalDictionary[it->second] = it->first;

	module->variableCount = max(tr.getTotalVarCount(), 1);

	return module;
}

void LayeredQBFProgram::printToStream(std::ostream &os) const
{
	const LayeredQBFProgram *lqp = this;
	int level = 0;
	while (lqp != NULL)
	{
		os << "###### LEVEL " << level << " ######" << endl;
		os << ((lqp->qType == Q_EXISTENTIAL) ? "exists " : "forall ");
		for (int j = 0; j < lqp->quantifiedVariables.size(); j++)
			os << lqp->quantifiedVariables[j] << " ";
		os << "0" << endl;

		for (int j = 0; j < lqp->definitions.size(); j++)
			os << "guard " << *(lqp->definitions[j]) << endl;

		for (int j = 0; j < lqp->guardingClauses.size(); j++)
			os << "guard " << *(lqp->guardingClauses[j]) << endl;

		for (int j = 0; j < lqp->clauses.size(); j++)
			os << "clause " << *(lqp->clauses[j]) << endl;

		level++;
		lqp = lqp->innerLayer;
	}
}

LayeredQBFProgram *addExistentialLayer(LayeredQBFProgram *lqp)
{
	if ((lqp == NULL) || (lqp->qType == Q_UNIVERSAL))
	{
		LayeredQBFProgram *temp = new LayeredQBFProgram();

		temp->qType = Q_EXISTENTIAL;
		temp->quantifiedVariables.push_back(Variable::makeVariable(1));
		temp->innerLayer = lqp;

		return temp;
	}
	else
		return lqp;
}

