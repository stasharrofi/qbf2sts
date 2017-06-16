//           qbfprogram.cc
//  Wed February 17 14:29:52 2016
//  Copyright  2016  Shahab Tasharrofi
//  <shahab.tasharrofi@gmail.com>
// qbfprogram.cc
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

#include <algorithm>
#include <assert.h>
#include <fstream>
#include <functional>
#include <iostream>
#include <sstream>
#include <sys/types.h>
#include <unistd.h>

#include "qbfprogram.h"
#include "utils.h"

#define DONT_PRINT_PROOF

int opt_extract_defs = 1;

ClauseDictionary::~ClauseDictionary()
{
	if (positiveAppearences != NULL)
		delete positiveAppearences; 
	if (negativeAppearences != NULL)
		delete negativeAppearences;
	if (nonAppearences != NULL)
		delete nonAppearences;
}

ClauseDictionary *ClauseIndexVector::insertClauseIntoDictionary(ClauseDictionary *clauseDic, Clause *newClause, Variable currentMinVar, int index)
{
	if ((clauseDic != NULL) && (currentMinVar > clauseDic->var))
	{
		clauseDic->nonAppearences = insertClauseIntoDictionary(clauseDic->nonAppearences, newClause, currentMinVar, index);
		return clauseDic;
	}

	if (clauseDic == NULL)
	{
		clauseDic = new ClauseDictionary();
		clauseDic->var = currentMinVar;
		clauseDic->location = -1;
		clauseDic->positiveAppearences = clauseDic->negativeAppearences = clauseDic->nonAppearences = NULL;
	}

	if (currentMinVar < clauseDic->var)
	{ // Should create a new node with current clauseDic in the nonAppearences part
		ClauseDictionary *newClauseDic = new ClauseDictionary();

		newClauseDic->var = currentMinVar;
		newClauseDic->location = -1;
		newClauseDic->positiveAppearences = newClauseDic->negativeAppearences = NULL;
		newClauseDic->nonAppearences = clauseDic;

		clauseDic = newClauseDic;
	}

	Variable nextMinVar = newClause->getNextMinimumVariable(currentMinVar);
	Sign s = newClause->getVariableSign(currentMinVar);
	ClauseDictionary *targetNode = ((s == SGN_POS) ? clauseDic->positiveAppearences : clauseDic->negativeAppearences);

	if (nextMinVar == currentMinVar)
	{ // End of clause
		if (targetNode == NULL)
		{
			targetNode = new ClauseDictionary();
			targetNode->var = currentMinVar;
			targetNode->positiveAppearences = targetNode->negativeAppearences = targetNode->nonAppearences = NULL;
		}

		targetNode->location = index;
	}
	else
		targetNode = insertClauseIntoDictionary(targetNode, newClause, nextMinVar, index);

	if (s == SGN_POS)
		clauseDic->positiveAppearences = targetNode;
	else
		clauseDic->negativeAppearences = targetNode;

	return clauseDic;
}

ClauseDictionary *ClauseIndexVector::findClauseDictionaryNode(Clause *clause)
{
	Variable minVar = clause->getNextMinimumVariable(Variable::makeVariable(0));
	ClauseDictionary *dicNode = clausesByMinVar[minVar.varNumber];
	while (dicNode != NULL)
	{
		if (dicNode->var > minVar)
			return NULL;
		else if (dicNode->var < minVar)
			dicNode = dicNode->nonAppearences;
		else
		{
			Sign s = clause->getVariableSign(minVar);
			dicNode = ((s == SGN_POS) ? dicNode->positiveAppearences : dicNode->negativeAppearences);
			Variable nextMinVar = clause->getNextMinimumVariable(minVar);
			if (minVar == nextMinVar)
				return dicNode;
			else
				minVar = nextMinVar;
		}
	}

	return NULL;
}

void ClauseIndexVector::insertClauseIndex(Clause *newClause, int index)
{
	Variable minVar = newClause->getNextMinimumVariable(Variable::makeVariable(0));
	if (minVar.varNumber == 0)
	{ // empty clause
		if (clausesByMinVar[0] == NULL)
		{
			clausesByMinVar[0] = new ClauseDictionary();
			clausesByMinVar[0]->var.varNumber = 0;
			clausesByMinVar[0]->location = index;
			clausesByMinVar[0]->positiveAppearences = clausesByMinVar[0]->negativeAppearences = clausesByMinVar[0]->nonAppearences = NULL;
		}
	}
	else
		clausesByMinVar[minVar.varNumber] = insertClauseIntoDictionary(clausesByMinVar[minVar.varNumber], newClause, minVar, index);
}

int ClauseIndexVector::findClauseIndex(Clause *clause)
{
	ClauseDictionary *dicNode = findClauseDictionaryNode(clause);
	if (dicNode != NULL)
		return dicNode->location;
	else
		return -1;
}

void ClauseIndexVector::updateClauseIndex(Clause *clause, int newIndex)
{
	ClauseDictionary *dicNode = findClauseDictionaryNode(clause);
	assert(dicNode != NULL);
	dicNode->location = newIndex;
}

ClauseIndexVector::~ClauseIndexVector()
{
	for (int i = 0; i < clausesByMinVar.size(); i++)
		if (clausesByMinVar[i] != NULL)
			delete clausesByMinVar[i];
}

Lit QBFProgram::getEquivalenceHead(Lit p)
{
	if (equalityGroup[p.var.varNumber - 1].var == p.var)
		return (p.sign == SGN_POS) ? equalityGroup[p.var.varNumber - 1] : equalityGroup[p.var.varNumber - 1].negated();

	Lit posP = getEquivalenceHead(equalityGroup[p.var.varNumber - 1]);
	equalityGroup[p.var.varNumber - 1] = posP;
	return (p.sign == SGN_POS) ? posP : posP.negated();
}

bool QBFProgram::assertLiteral(Lit p, bool checkUniversality)
{
	if (!okay)
		return false;
	if (getValue(p) == BV_TRUE)
		return true;
	if (getValue(p) == BV_FALSE)
	{
#ifdef PRINT_PROOF
		cerr << "c PROOF:" << p << ", " << p.negated() << " |= false" << endl;
#endif
		okay = false;
		return false;
	}
	if (checkUniversality && (!isGuarded(p.var)) && (getQuantifierType(p.var) == Q_UNIVERSAL))
	{
#ifdef PRINT_PROOF
		cerr << "c PROOF:" << p << ", universal(" << p.var << "), ~guarded(" << p.var << ") |= false" << endl;
#endif
		okay = false;
		return false;
	}

	setValue(p, BV_TRUE);
	assertionPropQueue.push(p);

	return true;
}

bool QBFProgram::assertEquivalence(Lit p, Lit q)
{
	if (!okay)
		return false;

#ifdef PRINT_PROOF
	cerr << "c PROOF:" << "(" << p << " = " << q << ")";
	if (p != getEquivalenceHead(p))
		cerr << ", (" << p << " = " << getEquivalenceHead(p) << ")";
	if (q != getEquivalenceHead(q))
		cerr << ", (" << q << " = " << getEquivalenceHead(q) << ")";
#endif
	p = getEquivalenceHead(p);
	q = getEquivalenceHead(q);

	if (getValue(p) != BV_UNKNOWN)
	{
#ifdef PRINT_PROOF
		if (getValue(p) == BV_TRUE)
			cerr << ", " << p << " |= " << q << " (assertion)" << endl;
		else
			cerr << ", " << p.negated() << " |= " << q.negated() << " (assertion)" << endl;
#endif
		return assertLiteral((getValue(p) == BV_TRUE) ? q : q.negated(), true);
	}
	if (getValue(q) != BV_UNKNOWN)
	{
#ifdef PRINT_PROOF
		if (getValue(q) == BV_TRUE)
			cerr << ", " << q << " |= " << p << " (assertion)" << endl;
		else
			cerr << ", " << q.negated() << " |= " << p.negated() << " (assertion)" << endl;
#endif
		return assertLiteral((getValue(q) == BV_TRUE) ? p : p.negated(), true);
	}

	if (p == q)
	{
#ifdef PRINT_PROOF
		cerr << " |= true (no operation)" << endl;
#endif
		return true;
	}
	if (p == q.negated())
	{
#ifdef PRINT_PROOF
		cerr << " |= false (inconsistency detected)" << endl;
#endif
		okay = false;
		return false;
	}

	if ((getVarLevel(p.var) < 0) && (getVarLevel(q.var) >= 0))
		updateVariableLevel(p.var, getVarLevel(q.var));
	if ((getVarLevel(q.var) < 0) && (getVarLevel(p.var) >= 0))
		updateVariableLevel(q.var, getVarLevel(p.var));

	// So, now, either both p and q have variable level >= 0 or they both have variable level < 0
	if ((0 <= getVarLevel(p.var)) && (getVarLevel(p.var) < getVarLevel(q.var)))
	{
		Lit temp = p;
		p = q;
		q = temp;
	}

	// Now, p is the variable that is being assigned
	if ((getVarLevel(p.var) >= 0) && (getVarLevel(p.var) > getVarLevel(q.var)) && (getQuantifierType(p.var) == Q_UNIVERSAL))
	{
#ifdef PRINT_PROOF
		cerr << ", universal(" << p.var << "), deeper(" << p.var << ") |= false (inconsistency detected)" << endl;
#endif
		okay = false;
		return false;
	}

#ifdef PRINT_PROOF
		cerr << " |= " << p << " = " << q << endl;
#endif

	setEquivalenceHead(p, q); // means that, from now on, every occurrence of p should be replaced by an occurrence of q
	equivalencePropQueue.push(pair<Lit, Lit>(p, q));

	return true;
}

void QBFProgram::propagateLiteral(Lit p)
{
#ifdef PRINT_PROOF
	cerr << "c PROOF:" << "// propagating literal " << p << endl;
#endif
	if (!okay)
		return;

#ifdef PRINT_PROOF
	if (p != getEquivalenceHead(p))
		cerr << "c PROOF:" << "(" << p << " = " << getEquivalenceHead(p) << "), " << p << " |= " << getEquivalenceHead(p) << endl << "c PROOF:// propagating literal " << getEquivalenceHead(p) << endl;
#endif

	p = getEquivalenceHead(p);
	Lit negP = p.negated();

	while (reverseClauseIndex[p.var.varNumber - 1].size() > 0)
	{
		bool sat = false;
		int index = *(reverseClauseIndex[p.var.varNumber - 1].cbegin());
		Clause *clause = clauses[index];
#ifdef PRINT_PROOF
		cerr << "c PROOF:" << p << ", (" << (*clause) << ")";
#endif
		removeClauseAtIndex(index);
		for (auto litIt = clause->begin(); litIt != clause->end(); litIt++)
			if (*litIt == p)
			{
				sat = true;
				break;
			}
			else if (*litIt == negP)
			{
				clause->erase(litIt, litIt + 1);
				break;
			}

		if (!sat)
		{
#ifdef PRINT_PROOF
			cerr << " |= " << (*clause) << " (replacing)" << endl;
#endif
			addClause(clause);
		}
		else
		{
#ifdef PRINT_PROOF
			cerr << " |= true (no operation)" << endl;
#endif
			delete clause;
		}
	}

	while (reverseDefinitionIndex[p.var.varNumber - 1].size() > 0)
	{
		int index = *(reverseDefinitionIndex[p.var.varNumber - 1].cbegin());
		Definition *def = definitions[index];
#ifdef PRINT_PROOF
		cerr << "c PROOF:" << p << ", (" << (*def) << ") |= ";
#endif
		removeDefinitionAtIndex(index);

		bool unsat = false;
		for (auto litIt = def->inputLiterals.begin(); litIt != def->inputLiterals.end(); litIt++)
			if (*litIt == negP)
			{
				unsat = true;
				break;
			}
			else if (*litIt == p)
			{
				def->inputLiterals.erase(litIt, litIt + 1);
				break;
			}

		if (unsat)
		{
#ifdef PRINT_PROOF
			cerr << def->outputLiteral << endl;
#endif
			if (!assertLiteral(def->outputLiteral, false))
				return; // inconsistency detected
			delete def;
		}
		else
		{
#ifdef PRINT_PROOF
			cerr << (*def) << endl;
#endif
			addDefinition(def);
		}
	}

	if (isGuarded(p.var))
	{ // expand definition of p.var according to value of "p".
		int index = getDefinitionIndex(p.var);
		Definition *def = definitions[index];
		removeDefinitionAtIndex(index);
		assert(def != NULL);
		assert(def->outputLiteral.var == p.var);

		if (def->outputLiteral == p)
		{
			Clause *clause = new Clause();
			for (auto litIt = def->inputLiterals.cbegin(); litIt != def->inputLiterals.cend(); litIt++)
				clause->push_back(litIt->negated());
#ifdef PRINT_PROOF
			cerr << "c PROOF:" << p << ", (" << (*def) << ") |= (" << (*clause) << ")" << endl;
#endif
			addClause(clause);
		}
		else
		{
			for (auto litIt = def->inputLiterals.cbegin(); litIt != def->inputLiterals.cend(); litIt++)
#ifdef PRINT_PROOF
				cerr << "c PROOF:" << p << ", (" << (*def) << ") |= " << (*litIt) << endl,
#endif
				assertLiteral(*litIt, true);
		}

		delete def;
	}
}

void QBFProgram::propagateEquivalence(Lit p, Lit q)
{
#ifdef PRINT_PROOF
	cerr << "c PROOF:" << "// propagating equivalence " << p << " = " << q << endl;
#endif
	if (!okay)
		return;

#ifdef PRINT_PROOF
	if (q != getEquivalenceHead(q))
		cerr << "c PROOF:" << "(" << p << " = " << q << "), (" << q << " = " << getEquivalenceHead(q) << ") |= (" << p << " = " << getEquivalenceHead(q) << ")" << endl << "c PROOF: // propagating equivalence " << p << " = " << getEquivalenceHead(q) << endl;
#endif

	Lit negP = p.negated();
	q = getEquivalenceHead(q);
	Lit negQ = q.negated();

	while (reverseClauseIndex[p.var.varNumber - 1].size() > 0)
	{
		int index = *(reverseClauseIndex[p.var.varNumber - 1].cbegin());
		Clause *clause = clauses[index];
#ifdef PRINT_PROOF
		cerr << "c PROOF:" << "(" << p << " = " << q << "), (" << (*clause) << ") |= ";
#endif
		removeClauseAtIndex(index);
		for (int i = 0; i < clause->size(); i++)
			if ((*clause)[i] == p)
			{
				(*clause)[i] = q;
				break;
			}
			else if ((*clause)[i] == negP)
			{
				(*clause)[i] = negQ;
				break;
			}

#ifdef PRINT_PROOF
		cerr << (*clause) << endl;
#endif
		addClause(clause);
	}

	while (reverseDefinitionIndex[p.var.varNumber - 1].size() > 0)
	{
		int index = *(reverseDefinitionIndex[p.var.varNumber - 1].cbegin());
		Definition *def = definitions[index];
#ifdef PRINT_PROOF
		cerr << "c PROOF:" << "(" << p << " = " << q << "), (" << (*def) << ") |= ";
#endif
		removeDefinitionAtIndex(index);

		for (int i = 0; i < def->inputLiterals.size(); i++)
			if (def->inputLiterals[i] == p)
			{
				def->inputLiterals[i] = q;
				break;
			}
			else if (def->inputLiterals[i] == negP)
			{
				def->inputLiterals[i] = negQ;
				break;
			}

#ifdef PRINT_PROOF
		cerr << (*def) << endl;
#endif
		addDefinition(def);
	}

	if (isGuarded(p.var))
	{ // expand definition of p.var according to value of "p".
		int index = getDefinitionIndex(p.var);
		Definition *def = definitions[index];
		removeDefinitionAtIndex(index);
		assert(def != NULL);
		assert(def->outputLiteral.var == p.var);

		Lit tempQ = (def->outputLiteral == p) ? q : negQ;
		Lit tempNegQ = tempQ.negated();

		Clause *clause = new Clause();
		clause->push_back(tempNegQ);
		for (auto litIt = def->inputLiterals.cbegin(); litIt != def->inputLiterals.cend(); litIt++)
			clause->push_back(litIt->negated());
#ifdef PRINT_PROOF
		cerr << "c PROOF:" << "(" << p << " = " << q << "), (" << (*def) << ") |= " << (*clause) << endl;
#endif
		addClause(clause);

		for (auto litIt = def->inputLiterals.cbegin(); litIt != def->inputLiterals.cend(); litIt++)
		{
			clause = new Clause();
			clause->push_back(tempQ);
			clause->push_back(*litIt);
#ifdef PRINT_PROOF
			cerr << "c PROOF:" << "(" << p << " = " << q << "), (" << (*def) << ") |= " << (*clause) << endl;
#endif
			addClause(clause);
		}

		delete def;
	}
}

void QBFProgram::extractEquivalences()
{
	Clause testClause;
	for (int i = 0; i < clauses.size(); i++)
		if (clauses[i]->size() == 2)
		{
			testClause.clear();
			testClause.push_back((*clauses[i])[0].negated());
			testClause.push_back((*clauses[i])[1].negated());
			int index = clauseIndex.findClauseIndex(&testClause);
			if (index >= 0)
			{
#ifdef PRINT_PROOF
				cerr << "c PROOF:(" << *(clauses[i]) << "), (" << testClause << ") |= " << testClause[0] << " = " << testClause[1].negated() << endl;
#endif
				if (!assertEquivalence(testClause[0], testClause[1].negated()))
					return;
			}
		}
}

void QBFProgram::extractForcedLiterals()
{
	unordered_set<Variable, Variable::hash> positivelyUsedVars;
	unordered_set<Variable, Variable::hash> negativelyUsedVars;
	std::function<void(Variable, bool)> markVar;
	markVar = [&positivelyUsedVars, &negativelyUsedVars, &markVar, this] (Variable var, bool pos) -> void
		{
			if (pos)
				if (positivelyUsedVars.count(var) > 0)
					return;
				else
					positivelyUsedVars.insert(var);
			else if (negativelyUsedVars.count(var) > 0)
				return;
			else negativelyUsedVars.insert(var);

			if (isGuarded(var))
			{
				assert(getDefinitionIndex(var) < definitions.size());
				Definition *def = definitions[getDefinitionIndex(var)];
				assert(def != NULL);
				assert(def->outputLiteral.var == var);
				for (auto it = def->inputLiterals.cbegin(); it != def->inputLiterals.cend(); it++)
					markVar(it->var, (it->sign == def->outputLiteral.sign)^pos);
			}
		};

	for (auto it = clauses.cbegin(); it != clauses.cend(); it++)
		for (auto litIt = (*it)->cbegin(); litIt != (*it)->cend(); litIt++)
			markVar(litIt->var, litIt->sign == SGN_POS);

	for (int i = 1; i <= variableCount; i++)
	{
		Variable curVar = Variable::makeVariable(i);
		if (!isGuarded(curVar) && (getValue(Lit::makeLiteral(curVar, SGN_POS)) == BV_UNKNOWN))
		{
			bool posUsed = (positivelyUsedVars.count(curVar) > 0);
			bool negUsed = (negativelyUsedVars.count(curVar) > 0);
			if (posUsed ^ negUsed)
			{
				Lit forcedLit = Lit::makeLiteral(curVar, ((getQuantifierType(curVar) == Q_UNIVERSAL) ^ negUsed) ? SGN_NEG : SGN_POS);
#ifdef PRINT_PROOF
				cerr << "c PROOF:" << "asserting literal " << forcedLit << " because it has been forced" << endl;
#endif
				assertLiteral(forcedLit, false);
			}
		}
	}
}

int QBFProgram::getClauseLevel(const Clause *clause) const
{
	int level = 0;

	for (auto it = clause->cbegin(); it != clause->cend(); it++)
		level = max(level, getVarLevel(it->var));

	return level;
}

int QBFProgram::getClauseExistentialLevel(const Clause *clause) const
{
	int level = -1;

	for (auto it = clause->cbegin(); it != clause->cend(); it++)
		if (getQuantifierType(it->var) == Q_EXISTENTIAL)
			level = max(level, getVarLevel(it->var));

	return level;
}

int QBFProgram::getClauseGuardLevel(const Clause *clause) const
{
	int level = -1;

	for (auto it = clause->cbegin(); it != clause->cend(); it++)
		if (isGuarded(it->var))
			level = max(level, getVarLevel(it->var));

	return level;
}

void QBFProgram::addVarToLastQuantifierLevel(Variable var)
{
	while (lastVar() < var)
		newVar();
	quantifiers[quantifiers.size() - 1]->variables.push_back(var);
	updateVariableLevel(var, quantifiers.size() - 1);
}

void QBFProgram::removeClauseAtIndex(int index)
{
	Clause *clause = clauses[index];
	clauseIndex.updateClauseIndex(clause, -1);

	for (auto it = clause->cbegin(); it != clause->cend(); it++)
		reverseClauseIndex[it->var.varNumber - 1].erase(index);

	int lastIndex = clauses.size() - 1;
	if (index < lastIndex)
	{
		clauseIndex.updateClauseIndex(clauses[lastIndex], index);
		clauses[index] = clauses[lastIndex];
		for (auto it = clauses[index]->cbegin(); it != clauses[index]->cend(); it++)
		{
			reverseClauseIndex[it->var.varNumber - 1].erase(lastIndex);
			reverseClauseIndex[it->var.varNumber - 1].insert(index);
		}
	}
	clauses.pop_back();
}

void QBFProgram::removeDefinitionAtIndex(int index)
{
	Definition *def = definitions[index];

	for (auto it = def->inputLiterals.cbegin(); it != def->inputLiterals.cend(); it++)
		reverseDefinitionIndex[it->var.varNumber - 1].erase(index);
	defIndex[def->outputLiteral.var.varNumber - 1] = -1; // the defined literal is no longer defined

	int lastIndex = definitions.size() - 1;
	if (index < lastIndex)
	{
		definitions[index] = definitions[lastIndex];
		for (auto it = definitions[index]->inputLiterals.cbegin(); it != definitions[index]->inputLiterals.cend(); it++)
		{
			reverseDefinitionIndex[it->var.varNumber - 1].erase(lastIndex);
			reverseDefinitionIndex[it->var.varNumber - 1].insert(index);
		}
		defIndex[definitions[index]->outputLiteral.var.varNumber - 1] = index;
	}
	definitions.pop_back();
}

void QBFProgram::updateVariableLevel(Variable var, int newLevel)
{
	setVarLevel(var, newLevel);
	for (auto it = reverseDefinitionIndex[var.varNumber - 1].cbegin(); it != reverseDefinitionIndex[var.varNumber - 1].cend(); it++)
	{
		Definition *def = definitions[*it];

		int defLevel = 0;
		for (int j = 0; j < def->inputLiterals.size(); j++)
			if (getVarLevel(def->inputLiterals[j].var) < 0)
			{
				defLevel = -1;
				break;
			}
			else if (getVarLevel(def->inputLiterals[j].var) > defLevel)
				defLevel = getVarLevel(def->inputLiterals[j].var);

		if ((defLevel >= 0) && (defLevel < getVarLevel(def->outputLiteral.var)))
			updateVariableLevel(def->outputLiteral.var, defLevel);
	}
}

void QBFProgram::newVar()
{
	variableCount++;
	varLevel.push_back(-1);
	defIndex.push_back(-1);
	values.push_back(BV_UNKNOWN);
	equalityGroup.push_back(Lit::makeLiteral(Variable::makeVariable(variableCount), SGN_POS));

	reverseDefinitionIndex.push_back(unordered_set<int>());
	reverseClauseIndex.push_back(unordered_set<int>());
	clauseIndex.newVar();
}

void QBFProgram::addClause(Clause *clause)
{
	for (auto it = clause->cbegin(); it != clause->cend(); it++)
		while (lastVar() < it->var)
			newVar();

	if (!okay)
	{
		delete clause;
		return;
	}

	// removing false literals and checking if the clause has a true literal
#ifdef PRINT_PROOF
	cerr << "c PROOF: (" << (*clause) << ")";
#endif
	int i = 0;
	for (int j = 0; j < clause->size(); j++)
		if (getValue((*clause)[j]) == BV_TRUE)
		{ // clause is already satisfied
#ifdef PRINT_PROOF
			cerr << ", " << (*clause)[j] << " |= true (clause purged)" << endl;
#endif
			delete clause;
			return;
		}
		else if (getValue((*clause)[j]) == BV_UNKNOWN)
		{ // unknown literals are moved to the front
			(*clause)[i] = (*clause)[j];
			i++;
		}
		else
		{
#ifdef PRINT_PROOF
			cerr << ", " << (*clause)[j].negated();
#endif
		}
	clause->erase(clause->begin() + i, clause->end()); // "i" is the new size of the clause after removing false literals

	// replacing literals with their equivalent
	for (int j = 0; j < clause->size(); j++)
	{
#ifdef PRINT_PROOF
		if ((*clause)[j] != getEquivalenceHead((*clause)[j]))
			cerr << ", " << (*clause)[j] << " = " << getEquivalenceHead((*clause)[j]);
#endif
		(*clause)[j] = getEquivalenceHead((*clause)[j]); // each literal is replace by the head of the equality group it belongs to
	}
#ifdef PRINT_PROOF
	cerr << " |= " << (*clause) << endl;
#endif

	sort(clause->begin(), clause->end(), Lit::literalSortFun);

	// removing duplicate literals
	if (clause->size() > 1)
	{
		i = 0;
		for (int j = 1; j < clause->size(); j++)
			if ((*clause)[i] != (*clause)[j])
			{
				i++;
				(*clause)[i] = (*clause)[j];
			}
		clause->erase(clause->begin() + i + 1, clause->end());
	}

	// checking if a literal and its negation are both present
	for (i = 1; i < clause->size(); i++)
		if ((*clause)[i-1].var == (*clause)[i].var)
		{
			delete clause;
			return;
		}

	int clauseLevel = getClauseLevel(clause);
	int maxUniversalLevel = max(getClauseExistentialLevel(clause), getClauseGuardLevel(clause));
	if (clauseLevel > maxUniversalLevel)
	{ // Using Q-Resolution rule of universal reduction, we can get rid
		// of those universally quantifies variables that are of level
		// higher than both "clauseExistsLevel" and "clauseGuardLevel"
		//
		// In order to see that "clauseExistsLevel" by itself is not sufficient,
		// look at the following example: !p ?q !r s:(s = p \/ r) ==> s \/ ~p
		// Here, "clauseExistsLevel" for (s \/ ~p) is -1 because it does not have
		// any existentially quantified variable. However, the clause is always
		// satisfied because it is equivalent to (p \/ r \/ ~p)
#ifdef PRINT_PROOF
		cerr << "c PROOF:(" << (*clause) << "), exist_level(" << (*clause) << ") = " << maxUniversalLevel;
#endif
		i = 0;
		for (int j = 0; j < clause->size(); j++)
			if (getVarLevel((*clause)[j].var) <= maxUniversalLevel)
			{
				(*clause)[i] = (*clause)[j];
				i++;
			}
#ifdef PRINT_PROOF
			else
				cerr << ", level(" << (*clause)[j] << ") = " << getVarLevel((*clause)[j].var);
#endif
		clause->erase(clause->begin() + i, clause->end());
#ifdef PRINT_PROOF
		cerr << " |= " << (*clause) << endl;
#endif
	}

	if (clause->size() == 0)
	{
#ifdef PRINT_PROOF
		cerr << "c PROOF:" << "inconsistency detected because of asserting clause of size zero" << endl;
#endif
		okay = false;
		delete clause;
		return;
	}

	if (clause->size() == 1)
	{ // the literal should only be asserted and not added to the database
		assertLiteral((*clause)[0], true);
		delete clause;
		return;
	}

	int clausePos = clauses.size();
	clauses.push_back(clause);
	clauseIndex.insertClauseIndex(clause, clausePos);
	for (auto it = clause->cbegin(); it != clause->cend(); it++)
		reverseClauseIndex[it->var.varNumber - 1].insert(clausePos);
}

void QBFProgram::addDefinition(Definition *def)
{
	while (lastVar() < def->outputLiteral.var)
		newVar();

	for (auto it = def->inputLiterals.cbegin(); it != def->inputLiterals.cend(); it++)
		while (lastVar() < it->var)
			newVar();

	if (!okay)
	{
		delete def;
		return;
	}

	// removing true literals and checking if the definition body contains a false literal
#ifdef PRINT_PROOF
	cerr << "c PROOF:(" << (*def) << ")";
#endif
	int i = 0;
	for (int j = 0; j < def->inputLiterals.size(); j++)
		if (getValue(def->inputLiterals[j]) == BV_FALSE)
		{ // definition body contains a false literal
#ifdef PRINT_PROOF
			cerr << ", " << def->inputLiterals[j].negated() << " |= " << def->outputLiteral << endl;
#endif
			assertLiteral(def->outputLiteral, false);
			delete def;
			return;
		}
		else if (getValue(def->inputLiterals[j]) == BV_UNKNOWN)
		{ // unknown literals are moved to the front
			def->inputLiterals[i] = def->inputLiterals[j];
			i++;
		}
		else
		{
#ifdef PRINT_PROOF
			cerr << ", " << def->inputLiterals[j];
#endif
		}
	def->inputLiterals.erase(def->inputLiterals.begin() + i, def->inputLiterals.end()); // "i" is the new size of the definition body after removing true literals

	// replacing literals with their equivalent
	for (int j = 0; j < def->inputLiterals.size(); j++)
	{
#ifdef PRINT_PROOF
		if (def->inputLiterals[j] != getEquivalenceHead(def->inputLiterals[j]))
			cerr << ", (" << def->inputLiterals[j] << " = " << getEquivalenceHead(def->inputLiterals[j]) << ")" << endl;
#endif
		def->inputLiterals[j] = getEquivalenceHead(def->inputLiterals[j]); // each literal is replace by the head of the equality group it belongs to
	}
#ifdef PRINT_PROOF
	cerr << " |= " << (*def) << endl;
#endif

	sort(def->inputLiterals.begin(), def->inputLiterals.end(), Lit::literalSortFun);

	// removing duplicate literals
	i = 0;
	for (int j = 1; j < def->inputLiterals.size(); j++)
		if (def->inputLiterals[i] != def->inputLiterals[j])
		{
			i++;
			def->inputLiterals[i] = def->inputLiterals[j];
		}
	def->inputLiterals.erase(def->inputLiterals.begin() + i + 1, def->inputLiterals.end());

	// checking if a literal and its negation are both present
	for (i = 1; i < def->inputLiterals.size(); i++)
		if (def->inputLiterals[i-1].var == def->inputLiterals[i].var)
		{
#ifdef PRINT_PROOF
			cerr << "c PROOF:(" << (*def) << ") |= " << def->outputLiteral << endl;
#endif
			assertLiteral(def->outputLiteral, false);
			delete def;
			return;
		}

	if (def->inputLiterals.size() == 0)
	{ // We are dealing with a definition p = nand() which is equivalent to asserting ~p
#ifdef PRINT_PROOF
		cerr << "c PROOF:(" << (*def) << ") |= " << endl;
#endif
		assertLiteral(def->outputLiteral.negated(), false);
		delete def;
		return;
	}

	if (def->inputLiterals.size() == 1)
	{ // We are dealing with a definition p = nand(q) which is asserting p = ~q
#ifdef PRINT_PROOF
		cerr << "c PROOF:(" << (*def) << ") |= " << def->outputLiteral << " = " << def->inputLiterals[0].negated() << endl;
#endif
		assertEquivalence(def->outputLiteral, def->inputLiterals[0].negated());
		delete def;
		return;
	}

	int newLevel = 0;
	int definitionIndex = definitions.size();
	definitions.push_back(def);
	for (auto it = def->inputLiterals.cbegin(); it != def->inputLiterals.cend(); it++)
	{
		while (lastVar() < it->var)
			newVar();
		if (getVarLevel(it->var) == -1)
			newLevel = -1;
		else if ((getVarLevel(it->var) > newLevel) && (newLevel >= 0))
			newLevel = getVarLevel(it->var);
		reverseDefinitionIndex[it->var.varNumber - 1].insert(definitionIndex);
	}
	defIndex[def->outputLiteral.var.varNumber - 1] = definitionIndex;

	if (newLevel >= 0)
		updateVariableLevel(def->outputLiteral.var, newLevel);
}

void QBFProgram::quantifyFreeVars()
{
	if (!okay)
		return;

	bool hasFreeVars = false;
	for (int i = 1; i <= variableCount; i++)
		if (getVarLevel(Variable::makeVariable(i)) < 0)
		{
			hasFreeVars = true;
			break;
		}

	if (!hasFreeVars)
		return;

	bool outerUniversal;
	if (quantifiers.size() == 0)
		outerUniversal = true;
	else
		outerUniversal = (quantifiers[0]->qType == Q_UNIVERSAL);

	if (!outerUniversal)
	{
		for (int i = 1; i <= variableCount; i++)
		{
			Variable currentVar = Variable::makeVariable(i);
			if (getVarLevel(currentVar) < 0)
			{
				quantifiers[0]->variables.push_back(currentVar);
				updateVariableLevel(currentVar, 0);
			}
		}
	}
	else
	{
		QuantifierBlock *quant = new QuantifierBlock();
		quant->qType = Q_EXISTENTIAL;
		for (int i = 1; i <= variableCount; i++)
		{
			Variable currentVar = Variable::makeVariable(i);
			if (getVarLevel(currentVar) < 0)
			{
				quant->variables.push_back(currentVar);
				setVarLevel(currentVar, 0);
			}
			else
				setVarLevel(currentVar, getVarLevel(currentVar) + 1);
		}
		quantifiers.insert(quantifiers.begin(), quant);
	}
}

void QBFProgram::simplifyDB()
{
	do
	{
		if (!okay)
			return;
		while (!assertionPropQueue.empty())
		{
			Lit p = assertionPropQueue.front();
			assertionPropQueue.pop();
			propagateLiteral(p);
		}
		while (!equivalencePropQueue.empty())
		{
			pair<Lit, Lit> equiv = equivalencePropQueue.front();
			equivalencePropQueue.pop();
			propagateEquivalence(equiv.first, equiv.second);
		}
		extractEquivalences();
		//extractForcedLiterals();
	}
	while ((!assertionPropQueue.empty()) || (!equivalencePropQueue.empty()));
}

void QBFProgram::extractDefinitions()
{
	Clause testClause;
	do
	{
		bool test = false;
		for (int i = 0; i < clauses.size(); i++)
		{
			Clause *currentClause = clauses[i];
			if (currentClause->size() < 2)
				continue;

			auto jt = currentClause->cbegin();
			Variable maxLevelVar = jt->var;
			Sign maxLevelVarSign = jt->sign;
			bool atLeastTwoMaxLevelVars = false;
			jt++;
			for (; jt != currentClause->cend(); jt++)
				if (getVarLevel(jt->var) > getVarLevel(maxLevelVar))
				{
					maxLevelVar = jt->var;
					maxLevelVarSign = jt->sign;
					atLeastTwoMaxLevelVars = false;
				}
				else if (getVarLevel(jt->var) == getVarLevel(maxLevelVar))
					atLeastTwoMaxLevelVars = true;

			if ((!atLeastTwoMaxLevelVars || (opt_extract_defs == 2)) && !isGuarded(maxLevelVar))
			{
				bool isDefinition = true;
				vector<int> toBeRemovedIndices;
				toBeRemovedIndices.push_back(i);
				for (jt = currentClause->cbegin(); jt != currentClause->cend(); jt++)
					if (jt->var != maxLevelVar)
					{
						testClause.clear();
						testClause.push_back(Lit::makeLiteral(maxLevelVar, maxLevelVarSign).negated());
						testClause.push_back(jt->negated());

						sort(testClause.begin(), testClause.end(), Lit::literalSortFun);

						int index = clauseIndex.findClauseIndex(&testClause);
						if (index < 0)
						{
							isDefinition = false;
							break;
						}
						else
							toBeRemovedIndices.push_back(index);
					}

				if (isDefinition)
				{
					test = true;
					Definition *newDef = new Definition();
					newDef->outputLiteral = Lit::makeLiteral(maxLevelVar, maxLevelVarSign).negated();

					for (jt = currentClause->cbegin(); jt != currentClause->cend(); jt++)
						if (jt->var != maxLevelVar)
							newDef->inputLiterals.push_back(jt->negated());

#ifdef PRINT_PROOF
					cerr << "c PROOF:";
					for (int j = 0; j < toBeRemovedIndices.size(); j++)
					{
						if (j > 0)
							cerr << ", ";
						cerr << "(" << (*(clauses[toBeRemovedIndices[j]])) << ")";
					}
					cerr << " |= " << (*newDef) << endl;
#endif
					addDefinition(newDef);

					sort(toBeRemovedIndices.begin(), toBeRemovedIndices.end(), std::greater<int>());
					for (int j = 0; j < toBeRemovedIndices.size(); j++)
					{
						Clause *toBeRemoveClause = clauses[toBeRemovedIndices[j]];
						removeClauseAtIndex(toBeRemovedIndices[j]);
						delete toBeRemoveClause;
					}
					i = max(0, i - toBeRemovedIndices.size());
				}
			}
		}

		if (!test)
			break;
	}
	while (true);
}

LayeredQBFProgram *QBFProgram::convertToLayeredQBFProgram(int level)
{
	if (!okay)
	{
		LayeredQBFProgram *falseProg = new LayeredQBFProgram();
		falseProg->innerLayer = NULL;

		falseProg->qType = Q_EXISTENTIAL;
		Variable v = Variable::makeVariable(1);
		falseProg->quantifiedVariables.push_back(v);

		Clause *c = new Clause();
		c->push_back(Lit::makeLiteral(v, SGN_POS));
		falseProg->clauses.push_back(c);

		c = new Clause();
		c->push_back(Lit::makeLiteral(v, SGN_NEG));
		falseProg->clauses.push_back(c);

		return falseProg;
	}

	if (level >= quantifiers.size())
		return NULL;

	LayeredQBFProgram *tempLayer = new LayeredQBFProgram();
	tempLayer->qType = quantifiers[level]->qType;
	tempLayer->innerLayer = NULL;

	for (int j = 1; j <= variableCount; j++)
	{
		Variable currentVar = Variable::makeVariable(j);
		if ((getVarLevel(currentVar) == level) && (!isGuarded(currentVar)) &&
		    (getValue(Lit::makeLiteral(currentVar, SGN_POS)) == BV_UNKNOWN) &&
		    (getEquivalenceHead(Lit::makeLiteral(currentVar, SGN_POS)).var == currentVar))
			tempLayer->quantifiedVariables.push_back(currentVar);
	}

	for (int j = 0; j < definitions.size(); j++)
		if (getVarLevel(definitions[j]->outputLiteral.var) == level)
			tempLayer->definitions.push_back(definitions[j]);

	for (int j = 0; j < guardingClauses.size(); j++)
		if (getClauseLevel(guardingClauses[j]) == level)
			tempLayer->guardingClauses.push_back(guardingClauses[j]);

	for (int j = 0; j < clauses.size(); j++)
		if (getClauseLevel(clauses[j]) == level)
			tempLayer->clauses.push_back(clauses[j]);

	LayeredQBFProgram *previousLayer = convertToLayeredQBFProgram(level + 1);
	if ((previousLayer != NULL) && (previousLayer->qType == tempLayer->qType))
	{
		previousLayer->quantifiedVariables.insert(previousLayer->quantifiedVariables.end(), tempLayer->quantifiedVariables.begin(), tempLayer->quantifiedVariables.end());
		previousLayer->definitions.insert(previousLayer->definitions.end(), tempLayer->definitions.begin(), tempLayer->definitions.end());
		previousLayer->clauses.insert(previousLayer->clauses.end(), tempLayer->clauses.begin(), tempLayer->clauses.end());

		delete tempLayer;

		tempLayer = previousLayer;
		previousLayer = tempLayer->innerLayer;
	}

	if ((previousLayer == NULL) && (tempLayer->clauses.size() == 0))
	{
		delete tempLayer;
		return NULL;
	}

	if ((tempLayer->qType == Q_UNIVERSAL) && ((previousLayer != NULL) || (tempLayer->clauses.size() > 1)))
	{
		if (previousLayer == NULL)
		{
			previousLayer = new LayeredQBFProgram();
			previousLayer->qType = Q_EXISTENTIAL;
			previousLayer->innerLayer = NULL;
			previousLayer->quantifiedVariables.clear();
			previousLayer->definitions.clear();
			previousLayer->clauses.clear();
		}

		previousLayer->clauses.insert(previousLayer->clauses.end(), tempLayer->clauses.begin(), tempLayer->clauses.end());
		tempLayer->clauses.clear();
	}

	tempLayer->innerLayer = previousLayer;

	return tempLayer;
}

void QBFProgram::decomposeLiteralSet(vector<Definition *> &newDefinitions, vector<Lit> &literals, bool isConjunction)
{
	if (literals.size() <= 1)
		return;

	auto layerBasedComparison = [this] (Lit p, Lit q) -> bool
		{
			if (getVarLevel(p.var) < getVarLevel(q.var))
				return true;
			else if (getVarLevel(p.var) > getVarLevel(q.var))
				return false;
			else
				return Lit::literalSortFun(p, q);
		};
	std::sort(literals.begin(), literals.end(), layerBasedComparison);

	int startIndex = 0;
	int lastIndex = 1;
	Lit lastLiteral;
	Clause newLiterals;
	while (startIndex < literals.size())
	{
		while (lastIndex < literals.size())
		{ // finds the range of literals that have the same level; the range would be [startIndex ... lastIndex-1]
			if (getVarLevel(literals[lastIndex].var) > getVarLevel(literals[startIndex].var))
				break;
			else
				lastIndex++;
		}

		newLiterals.clear();
		if (startIndex > 0)
			newLiterals.push_back(lastLiteral);
		while (startIndex < lastIndex)
		{
			newLiterals.push_back(literals[startIndex]);
			startIndex++;
		}

		if (lastIndex >= literals.size())
		{
			literals = newLiterals;
			break;
		}
		else if (newLiterals.size() >= 2)
		{
			newVar();
			lastLiteral = Lit::makeLiteral(lastVar(), SGN_POS);

			Definition *newDef = new Definition();
			newDef->outputLiteral = (isConjunction ? lastLiteral.negated() : lastLiteral);
			for (auto it = newLiterals.cbegin(); it != newLiterals.cend(); it++)
				newDef->inputLiterals.push_back(isConjunction ? *it : it->negated());

			addDefinition(newDef);
		}
		else
			lastLiteral = newLiterals[0];

		lastIndex++;
	}
}

void QBFProgram::extendLearningLanguage()
{
	vector<Definition *> newDefinitions;

	for (int i = 0; i < clauses.size(); i++)
		decomposeLiteralSet(newDefinitions, *(clauses[i]), false);
	for (int i = 0; i < definitions.size(); i++)
		decomposeLiteralSet(newDefinitions, definitions[i]->inputLiterals, true);

	definitions.insert(definitions.end(), newDefinitions.begin(), newDefinitions.end());
}

void QBFProgram::breakSymmetries(string *breakIDPath, int timeLimit)
{
	string cnfFileName = tmpnam(nullptr);
	string fixedVarsFileName = tmpnam(nullptr);
	string symClausesFileName = tmpnam(nullptr);

	std::filebuf cnfFileBuf;
	cnfFileBuf.open(cnfFileName, std::ios::out);
	if (!cnfFileBuf.is_open())
		fprintf(stderr, "ERROR: unable to write temporary cnf file.\n"), exit(-1);
	std::ostream cnf(&cnfFileBuf);

	int clauseCount = clauses.size();
	for (auto it = definitions.cbegin(); it != definitions.cend(); it++)
		clauseCount += 1 + (*it)->inputLiterals.size();
	cnf << "p cnf " << variableCount << " " << clauseCount << endl;

	int initialVarCount = variableCount;
	for (auto it = clauses.cbegin(); it != clauses.cend(); it++)
		cnf << **it << endl;

	Clause clause;
	for (auto it = definitions.cbegin(); it != definitions.cend(); it++)
	{
		Definition *def = *it;
		clause.clear();
		clause.push_back(def->outputLiteral.negated());
		for (auto litIt = def->inputLiterals.cbegin(); litIt != def->inputLiterals.cend(); litIt++)
			clause.push_back(*litIt);
		cnf << clause << endl;

		for (auto litIt = def->inputLiterals.cbegin(); litIt != def->inputLiterals.cend(); litIt++)
		{
			clause.clear();
			clause.push_back(def->outputLiteral);
			clause.push_back(litIt->negated());
			cnf << clause << endl;
		}
	}
	cnfFileBuf.close();

	int maxLevel = 1;
	for (auto it = varLevel.cbegin(); it != varLevel.cend(); it++)
		if (maxLevel <= *it)
			maxLevel = *it + 1;

	if (!system(NULL))
		fprintf(stderr, "ERROR! Command processor not available.\n"), exit(-1);

	stringstream commandBuilder;
	commandBuilder << (*breakIDPath) << " " << cnfFileName << " -t " << timeLimit << " -v 0 -fixed " << fixedVarsFileName << " -print-only-breakers | sed '/^c/d' >" << symClausesFileName;
	string command = commandBuilder.str();

	std::filebuf fixedVarFileBuf;
	std::filebuf symClausesFileBuf;
	for (int level = 0; level < maxLevel; level++)
	{
		fixedVarFileBuf.open(fixedVarsFileName, std::ios::out);
		if (!fixedVarFileBuf.is_open())
			fprintf(stderr, "ERROR! unable to write temporary fixed vars file.\n"), exit(-1);
		std::ostream fixedVars(&fixedVarFileBuf);
		int varCountDifference = variableCount - initialVarCount;

		for (int varNum = 1; varNum <= variableCount; varNum++)
		{
			Variable var = Variable::makeVariable(varNum);
			if (getVarLevel(var) != level)
				fixedVars << var << " ";
			else if (getValue(Lit::makeLiteral(var, SGN_POS)) != BV_UNKNOWN)
				fixedVars << var << " ";
			else if (getEquivalenceHead(Lit::makeLiteral(var, SGN_POS)).var != var)
				fixedVars << var << " ";
		}
		fixedVarFileBuf.close();

		if (system(NULL) == 0)
			fprintf(stderr, "ERROR! no command processor available to run BreakID.\n"), exit(-1);
		if (system(command.c_str()) != 0)
			fprintf(stderr, "ERROR! running BreakID returned nonzero value.\n"), exit(-1);
		
		symClausesFileBuf.open(symClausesFileName, std::ios::in);
		if (!symClausesFileBuf.is_open())
			fprintf(stderr, "ERROR! unable to read output file from BreakID.\n"), exit(-1);
		std::istream scFile(&symClausesFileBuf);

		while (scFile.peek() != std::char_traits<char>::eof())
		{
			int pNum = 0;
			Clause *clause = new Clause();
			scFile >> pNum;
			while (pNum != 0)
			{
				int pVarNum = abs(pNum);
				bool pSign = (pNum > 0);
				if (pVarNum > initialVarCount)
					pVarNum += varCountDifference;
				Lit p = Lit::makeLiteral(Variable::makeVariable(pVarNum), pSign ? SGN_POS : SGN_NEG);
				while (lastVar() < p.var)
				{
					newVar();
					updateVariableLevel(lastVar(), level);
				}
				clause->push_back(p);
				scFile >> pNum;
			}
			if (clause->size() > 0)
				guardingClauses.push_back(clause);
			else
				delete clause;
		}
		symClausesFileBuf.close();
	}
	if (::remove(cnfFileName.c_str()) != 0)
		fprintf(stderr, "ERROR! Temporary CNF file cannot be removed.\n");
	if (::remove(fixedVarsFileName.c_str()) != 0)
		fprintf(stderr, "ERROR! Temporary file for fixed vars cannot be removed.\n");
	if (::remove(symClausesFileName.c_str()) != 0)
		fprintf(stderr, "ERROR! Temporary file for symmetry breaking clauses cannot be removed.\n");
}

void QBFProgram::printToStream(ostream &os) const
{
	for (int i = 0; i < quantifiers.size(); i++)
	{
		os << "###### LEVEL " << i << " ######" << endl;
		os << ((quantifiers[i]->qType == Q_EXISTENTIAL) ? "exists " : "forall ");
		for (int j = 0; j < quantifiers[i]->variables.size(); j++)
			if (getVarLevel(quantifiers[i]->variables[j]) == i)
				os << quantifiers[i]->variables[j] << " ";
		os << "0" << endl;

		for (int j = 0; j < definitions.size(); j++)
			if (getVarLevel(definitions[j]->outputLiteral.var) == i)
				os << "guard " << *(definitions[j]) << endl;

		for (int j = 0; j < guardingClauses.size(); j++)
			if (getClauseLevel(guardingClauses[j]) == i)
				os << "guard " << *(guardingClauses[j]) << endl;

		for (int j = 0; j < clauses.size(); j++)
			if (getClauseLevel(clauses[j]) == i)
				os << "clause " << *(clauses[j]) << endl;
	}
}

QBFProgram::QBFProgram()
{
	variableCount = 0;
}

QBFProgram::~QBFProgram()
{
	for (int i = 0; i < quantifiers.size(); i++)
		delete quantifiers[i];
}

