/***************************************************************************
 *            qbfprogram.h
 *
 *  Wed February 17 14:29:53 2016
 *  Copyright  2016  Shahab Tasharrofi
 *  <shahab.tasharrofi@gmail.com>
 ****************************************************************************/
/*
 * qbfprogram.h
 *
 * Copyright (C) 2016 - Shahab Tasharrofi
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef _QBF_PROGRAM_H
#define _QBF_PROGRAM_H

#include <queue>
#include <unordered_set>

#include "core.h"
#include "layeredqbf.h"

extern int opt_extract_defs;	// 0 --> no definition extraction
															// 1 --> only those definitions that change quantification level of a variable
															// 2 --> all definitions

struct ClauseDictionary {
	Variable var; // The decision variable; zero means a leaf node
	int location; // Index (in the CNF program) of the clause that ended in this node 

	ClauseDictionary *positiveAppearences; // subset of clauses that contain "var" positively; NULL if empty 
	ClauseDictionary *negativeAppearences; // subset of clauses that contain "var" negatively; NULL if empty
	ClauseDictionary *nonAppearences; // subset of clauses that do not contain "var"; NULL if empty

	~ClauseDictionary();
};

struct ClauseIndexVector
{
	public:
		vector<ClauseDictionary *> clausesByMinVar; // Each clause is indexed at the position of its minimum variable index; Empty clause is at position 0
	private:
		// requires that variable be present in the clause
		// requires that clause be sorted
		ClauseDictionary *insertClauseIntoDictionary(ClauseDictionary *clauseDic, Clause *newClause, Variable currentMinVar, int index);

		// requires that clause be sorted
		ClauseDictionary *findClauseDictionaryNode(Clause *clause);
	public:
		void newVar() { clausesByMinVar.push_back(NULL); }

		// requires that clause be sorted
		void insertClauseIndex(Clause *newClause, int index);

		// requires that clause be sorted
		int findClauseIndex(Clause *clause);

		// requires that clause be sorted
		void updateClauseIndex(Clause *clause, int newIndex);

		ClauseIndexVector() { clausesByMinVar.push_back(NULL); }
		~ClauseIndexVector();
};

struct QuantifierBlock
{
	QuantifierType qType;
	vector<Variable> variables;
};

struct QBFProgram
{
	private:
		bool okay = true; // okay becomes false if we detect unsatisfiability
		int variableCount;
		vector<QuantifierBlock *> quantifiers;
		CNFProgram clauses;
		CNFProgram guardingClauses;

		vector<int> varLevel; // level[i] is the level of variable v_i
		vector<int> defIndex; // defIndex[i] >= 0 means that v_i is the output of definition stored at definitions[defIndex[i]]
													// defIndex[i] < 0 means that v_i is not the output of any definition
		vector<BoolValue> values; // values[i] in {BV_TRUE, BV_FALSE} means that value of v_i is known
															// values[i] == BV_UNKNOWN means that value of v_i is not known yet!
		vector<Lit> equalityGroup;	// equalityGroup[i] == p means that variable v_i is equivalent to literal p
																// It is guaranteed that if equalityGroup[i] == p then v_i does not appear
																// anywhere else in the program
																// The head of a group is denoted using equalityGroup[i] == v_i
		ClauseIndexVector clauseIndex; // clauseIndex[v] is the index of all clauses with minimum variable "v"

		vector<Definition *> definitions;
		vector< unordered_set<int> > reverseDefinitionIndex;	// if reverseDefinitionIndex[j] contains index i, it means that the i-th
																													// definition (in the definitions vector) uses variable v_j as an input
		vector< unordered_set<int> > reverseClauseIndex;	// if reverseClauseIndex[j] contains index i, it means that the i-th clause
																											// (in the clauses vector) uses variable v_j
		queue<Lit> assertionPropQueue;
		queue< pair<Lit, Lit> > equivalencePropQueue; // (p, q) in equivalencePropQueue means that occurrences of p should be replaced
																									// by occurrences of q

		QuantifierType getQuantifierType(const Variable var) const { int n = getVarLevel(var); return (n < 0) ? Q_EXISTENTIAL : quantifiers[n]->qType; }
		int getDefinitionIndex(Variable var) { return defIndex[var.varNumber - 1]; }

		Lit getEquivalenceHead(Lit p);
		void setEquivalenceHead(Variable var, Lit p) { Lit q = getEquivalenceHead(Lit::makeLiteral(var, SGN_POS)); equalityGroup[q.var.varNumber - 1] = (q.sign == SGN_POS) ? p : p.negated(); }
		void setEquivalenceHead(Lit p, Lit q) { setEquivalenceHead(p.var, (p.sign == SGN_POS) ? q : q.negated()); }

		BoolValue getValue(Lit p) { p = getEquivalenceHead(p); return (p.sign == SGN_NEG) ? negation(values[p.var.varNumber - 1]) : values[p.var.varNumber - 1]; }
		void setValue(Lit p, BoolValue bv) { p = getEquivalenceHead(p); values[p.var.varNumber - 1] = ((p.sign == SGN_NEG) ? negation(bv) : bv); }

		bool assertLiteral(Lit p, bool checkUniversality); // puts literal p in assertionPropQueue if necessary; returns false if inconsistency detected
		bool assertEquivalence(Lit p, Lit q); // puts equivalence p=q in equivalencePropQueue if necessary; returns false if inconsistency detected
		void propagateLiteral(Lit p);
		void propagateEquivalence(Lit p, Lit q);

		void extractEquivalences();
		void extractForcedLiterals();

		void removeClauseAtIndex(int index);
		void removeDefinitionAtIndex(int index);
	public:
		inline Variable lastVar() { return Variable::makeVariable(variableCount); }
		inline int getVarLevel(const Variable var) const { return varLevel[var.varNumber - 1]; }
		inline void setVarLevel(Variable var, int level){ varLevel[var.varNumber - 1] = level; }
		int getClauseLevel(const Clause *clause) const;
		int getClauseExistentialLevel(const Clause *clause) const; // returns -1 if the clause has no existentially quantified variable
		int getClauseGuardLevel(const Clause *clause) const; // returns -1 if the clause has no guarded variable

		inline int levelCount() { return quantifiers.size(); }
		inline void newQuantifierLevel(QuantifierType qType) { QuantifierBlock *qb = new QuantifierBlock(); qb->qType = qType; quantifiers.push_back(qb); }
		void addVarToLastQuantifierLevel(Variable var);

		inline bool isGuarded(Variable var) const { return defIndex[var.varNumber - 1] >= 0; }

		void updateVariableLevel(Variable var, int newLevel);

		void newVar();
		void addClause(Clause *clause);
		void addDefinition(Definition *def);

		void quantifyFreeVars();
		void simplifyDB();
		void extractDefinitions();
		void decomposeLiteralSet(vector<Definition *> &newDefinitions, vector<Lit> &literals, bool isConjunction);
		void extendLearningLanguage();
		void breakSymmetries(string *breakIDPath, int timeLimit);

		LayeredQBFProgram *convertToLayeredQBFProgram(int level);

		void printToStream(ostream &os) const;

		QBFProgram();
		~QBFProgram();
};

inline std::ostream& operator<<(std::ostream& os, const QBFProgram &program) { program.printToStream(os); return os; }

#endif
