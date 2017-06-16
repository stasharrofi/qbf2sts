/***************************************************************************
 *            core.h
 *
 *  Wed February 17 14:10:05 2016
 *  Copyright  2016  Shahab Tasharrofi
 *  <shahab.tasharrofi@gmail.com>
 ****************************************************************************/
/*
 * cnf.h
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

#ifndef _CNF_H
#define _CNF_H

#include <vector>
#include <iostream>

using namespace std;

enum BoolValue
{
	BV_TRUE = 1,
	BV_UNKNOWN = 0,
	BV_FALSE = -1
};

enum Sign
{
	SGN_POS,
	SGN_NEG
};

struct Variable
{
  struct hash
  {
    std::size_t operator()(const Variable& v) const { return std::hash<int>()(v.varNumber); }
  };

	int varNumber;

	static Variable makeVariable(int varNum) { Variable v; v.varNumber = varNum; return v; }

	inline bool operator<(const Variable &v) const { return varNumber < v.varNumber; }
	inline bool operator<=(const Variable &v) const { return varNumber <= v.varNumber; }
	inline bool operator>(const Variable &v) const { return varNumber > v.varNumber; }
	inline bool operator>=(const Variable &v) const { return varNumber >= v.varNumber; }
	inline bool operator==(const Variable &v) const { return varNumber == v.varNumber; }
	inline bool operator!=(const Variable &v) const { return varNumber != v.varNumber; }

	Variable() {}
	Variable(const Variable &v) : varNumber(v.varNumber) {}
};

struct Lit
{
	Sign sign;
	Variable var;

	static Lit makeLiteral(Variable var, Sign s);
	Lit negated() const;
	static bool literalSortFun(Lit p, Lit q);

	inline bool operator<(const Lit &p) const { return literalSortFun(*this, p); }
	inline bool operator!=(const Lit &p) const { return (var != p.var) || (sign != p.sign); }
	inline bool operator==(const Lit &p) const { return (var == p.var) && (sign == p.sign); }

	Lit() {}
	Lit(const Lit &p) : sign(p.sign), var(p.var) {}
};

struct Clause : vector<Lit>
{
	Clause() {}
	Clause(const vector<Lit> &clause) : vector<Lit>(clause) {}

	// requires that variable be present in the clause
	// requires that clause be sorted
	int findVariablePositionInClause(Variable var);

	// requires that currentMinVar be either present in the clause or zero
	// requires that clause be sorted
	Variable getNextMinimumVariable(Variable currentMinVar);

	// requires that variable be present in the clause
	// requires that clause be sorted
	Sign getVariableSign(Variable var);

	void printToStream(std::ostream &os) const;
};

typedef vector<Clause *> CNFProgram;

struct Definition
{ // A definition is always a NAND, i.e., outputLiteral := NAND(inputLiteral_1, ...., inputLiteral_n)
	//
	// p == p1 /\ p2 /\ ... /\ pN is described as ~p == NAND(p1, p2, ..., pN)
	//
	// p == p1 \/ p2 \/ ... \/ pN is described as p == NAND(~p1, ~p2, ..., ~pN)
	//
	// p == p' is described as ~p == NAND(p')
	//
	// p == ~p' is described as p == NAND(p')
	//
	// p == NAND(p1, ..., pN) is defined as follows:
	// p \/ pI (for 1 <= I <= N)
	// ~p1 \/ ~p2 \/ ... \/ ~pN \/ ~p
	Lit outputLiteral;
	vector<Lit> inputLiterals;

	Definition() {}
	Definition(const Lit &outLit, const vector<Lit> &inLits) : outputLiteral(outLit), inputLiterals(inLits) {}

	void printToStream(std::ostream &os) const;
};

enum QuantifierType
{
	Q_EXISTENTIAL,
	Q_UNIVERSAL
};

inline BoolValue negation(BoolValue bv) { return (bv == BV_TRUE) ? BV_FALSE : ((bv == BV_FALSE) ? BV_TRUE : BV_UNKNOWN); }

inline std::ostream& operator<<(std::ostream& os, const Variable &v) { os << v.varNumber; return os; }
inline std::ostream& operator<<(std::ostream& os, const Lit &p) { os << ((p.sign == SGN_NEG) ? "-" : "") << p.var; return os; }
inline std::ostream& operator<<(std::ostream& os, const Clause &clause) { clause.printToStream(os); return os; }
inline std::ostream& operator<<(std::ostream& os, const Definition &def) { def.printToStream(os); return os; }


#endif
