/***************************************************************************
 *            stsmodule.h
 *
 *  Thu June 1 2017
 *  Copyright  2017  Shahab Tasharrofi
 *  <shahab.tasharrofi@gmail.com>
 ****************************************************************************/
/*
 * stsmodule.h
 *
 * Copyright (C) 2017 - Shahab Tasharrofi
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

#ifndef _STS_PROP_MODULE_H
#define _STS_PROP_MODULE_H

#include <unordered_map>

struct STSPropagatorModule;

struct NegativePropagatorSubmodule
{
	STSPropagatorModule *submodule;
	vector<Variable> positiveBindings;
	vector<Variable> negativeBindings;
};

struct STSPropagatorModule
{
	int moduleNo, variableCount;

	unordered_map<Variable, Variable, Variable::hash> positiveDictionary; // positiveDictionary[i] = j means that input variable "v_i" of this module
																																				// represents positive occurrences of variable "v_j" in the original CNF
	unordered_map<Variable, Variable, Variable::hash> negativeDictionary; // negativeDictionary[i] = j means that input variable "v_i" of this module
																																				// represents negative occurrences of variable "v_j" in the original CNF
	unordered_map<Variable, Variable, Variable::hash> internalDictionary; // internalDictionary[i] = j means that input variable "v_i" of this module
																																				// represents internal occurrences of variable "v_j" in the original CNF
	
	vector<Variable> positiveInputVariables;
	vector<Variable> negativeInputVariables;

	CNFProgram clauses;

	vector<NegativePropagatorSubmodule *> negativeSubmodules;
};

#endif
