/***************************************************************************
 *            stsmodule.h
 *
 *  Wed February 17 16:37:09 2016
 *  Copyright  2016  Shahab Tasharrofi
 *  <shahab.tasharrofi@gmail.com>
 ****************************************************************************/
/*
 * stsmodule.h
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

#ifndef _STS_MODULE_H
#define _STS_MODULE_H

#include <unordered_map>

struct STSModule;

struct NegativeSubmodule
{
	STSModule *submodule;
	vector<Variable> bindings;
};

struct STSModule
{
	int moduleNo, variableCount;

	// externalDictionary[i] = j means that input variable "v_i" of this module
	// represents occurrences of variable "v_j" in the original CNF
	unordered_map<Variable, Variable, Variable::hash> externalDictionary;
	// internalDictionary[i] = j means that input variable "v_i" of this module
	// represents internal occurrences of variable "v_j" in the original CNF
	unordered_map<Variable, Variable, Variable::hash> internalDictionary;

	// inputVariables[i] = <v, <b1, b2> > means that:
	// (1) v is the internal variable that constitutes the i-th input to this module
	// (2) this module uses v positively if and only if b1 holds
	// (3) this module uses v negatively if and only if b2 holds
	vector<pair<Variable, pair<bool, bool> > > inputVariables;

	CNFProgram clauses;

	vector<NegativeSubmodule *> negativeSubmodules;
};

#endif
