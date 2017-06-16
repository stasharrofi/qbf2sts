//           core.cc
//  Wed February 17 14:10:05 2016
//  Copyright  2016  Shahab Tasharrofi
//  <shahab.tasharrofi@gmail.com>
// cnf.cc
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

#include "core.h"

Lit Lit::makeLiteral(Variable var, Sign s)
{
	Lit p;

	p.sign = s;
	p.var = var;

	return p;
}

Lit Lit::negated() const
{
	Lit p;

	p.sign = (sign == SGN_POS) ? SGN_NEG : SGN_POS;
	p.var = var;

	return p;
}

bool Lit::literalSortFun(Lit p, Lit q)
{
	if (p.var < q.var)
		return true;
	else if ((p.var == q.var) && (p.sign == SGN_NEG) && (q.sign == SGN_POS))
		return true;
	else
		return false;
}

int Clause::findVariablePositionInClause(Variable var)
{
	int l = 0, u = size();
	int m = (l + u) / 2;
	while (l < u)
	{
		Variable currentVar = (*this)[m].var;
		if (currentVar < var)
			l = m + 1;
		else if (currentVar > var)
			u = m;
		else
			break;

		m = (l + u) / 2;
	}

	assert(l < u);
	assert((*this)[m].var == var);

	return m;
}

Variable Clause::getNextMinimumVariable(Variable currentMinVar)
{
	if (size() == 0)
		return Variable::makeVariable(0);
	if (currentMinVar < (*this)[0].var)
		return (*this)[0].var;
	if (currentMinVar >= (*this)[size() - 1].var)
		return currentMinVar;

	int pos = findVariablePositionInClause(currentMinVar);
	assert(pos + 1 < size());

	return (*this)[pos + 1].var;
}

Sign Clause::getVariableSign(Variable var)
{
	int pos = findVariablePositionInClause(var);
	return (*this)[pos].sign;
}

void Clause::printToStream(std::ostream &os) const
{
	for (auto it = cbegin(); it != cend(); it++)
		os << (*it) << " ";
	os << "0";
}

void Definition::printToStream(std::ostream &os) const
{
	os << outputLiteral << " = nand(";
	for (int k = 0; k < inputLiterals.size(); k++)
		os << ((k > 0) ? ", " : "") << inputLiterals[k];
	os << ")";
}
