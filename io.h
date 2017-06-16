/***************************************************************************
 *            io.h
 *
 *  Wed February 17 13:42:13 2016
 *  Copyright  2016  Shahab Tasharrofi
 *  <shahab.tasharrofi@gmail.com>
 ****************************************************************************/
/*
 * io.h
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

#ifndef _IO_H
#define _IO_H

#include "stdio.h"
#include "stdlib.h"

#include <iostream>

#include "qbfprogram.h"

extern int opt_confl_min_level;
extern int opt_confl_min_tries;

enum OutputStyle
{
	STYLE_DIMACS,
	STYLE_TEXT
};

QBFProgram *readQDimacs(FILE *in);
QBFProgram *readPrenexQCIR(FILE *in);

std::ostream& operator<<(std::ostream& os, const Variable &v);
std::ostream& operator<<(std::ostream& os, const Lit &p);
std::ostream& operator<<(std::ostream& os, const Clause &clause);
std::ostream& operator<<(std::ostream& os, const Definition &def);

void printClauseDictionary(std::ostream& os, int tab, ClauseDictionary *node);
std::ostream& operator<<(std::ostream& os, const ClauseIndexVector &clauseIndices);

std::ostream& operator<<(std::ostream& os, const QBFProgram &program);
std::ostream& operator<<(std::ostream& os, const LayeredQBFProgram *lqp);
void printSTSPropagatorModule(std::ostream& os, OutputStyle style, STSPropagatorModule *module, bool topModule);
void printSTSModule(std::ostream& os, OutputStyle style, STSModule *module, bool topModule);

#endif
