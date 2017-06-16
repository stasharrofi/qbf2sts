/***************************************************************************
 *            layeredqbf.h
 *
 *  Wed February 17 17:09:57 2016
 *  Copyright  2016  Shahab Tasharrofi
 *  <shahab.tasharrofi@gmail.com>
 ****************************************************************************/
/*
 * layeredqbf.h
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

#ifndef _LAYERED_QBF_H
#define _LAYERED_QBF_H

#include "core.h"
#include "stsmodule.h"
#include "stspropmodule.h"

extern bool opt_optimize_defs;

struct LayeredQBFProgram
{
	QuantifierType qType;

	vector<Variable> quantifiedVariables;
	vector<Definition *> definitions;

	CNFProgram clauses;
	CNFProgram guardingClauses;

	LayeredQBFProgram *innerLayer;

	STSPropagatorModule *convertToSTSProp(int &nextAvailableModuleNo);
	STSModule *convertToSTS(int &nextAvailableModuleNo);

	void printToStream(std::ostream &os) const;
};

inline std::ostream& operator<<(std::ostream& os, const LayeredQBFProgram &lqp) { lqp.printToStream(os); return os; }

LayeredQBFProgram *addExistentialLayer(LayeredQBFProgram *);

#endif
