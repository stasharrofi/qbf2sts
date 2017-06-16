/* -*- Mode: C; indent-tabs-mode: t; c-basic-offset: 2; tab-width: 2 -*-  */
/*
 * main.cc
 * Copyright (C) 2015 Shahab Tasharrofi <shahab.tasharrofi@gmail.com>
 * 
 * qbf2sts is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * sts-simplifier is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "string.h"

#include <stdio.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <unordered_set>
#include <utility>

#include "io.h"
#include "stsmodule.h"
#include "layeredqbf.h"
#include "qbfprogram.h"

bool opt_ext_language = false;
bool opt_simplify_db = true;
bool opt_break_symmetries = false;
int opt_sym_break_time = 30;
string *opt_sym_breaker_path;
int opt_input_format = 0; // 0 --> QDIMACS input format
													// 1 --> QCIR input format
int opt_output_format = 0; // 0 --> SAT-to-SAT Propagator-based format
													 // 1 --> SAT-to-SAT Module-based format

using namespace std;

QBFProgram *readInput(FILE *in)
{
	if (opt_input_format == 0)
		return readQDimacs(in);
	else
		return readPrenexQCIR(in);
}

void printUsage()
{
	printf("qbf2sts:\n");
	printf("  reads qdimacs input from 'stdin' and writes its sat-to-sat\n");
	printf("  representation into 'stdout'.\n");
	printf("usage:\n");
	printf("  ./qbf2sts [-ext-lang] [-h]\n");
	printf("options:\n");
	printf("  -ext-lang        : introduce new Tseiten variables to model extended\n");
	printf("                     language of learning in the SAT solvers.\n");
	printf("  -ext-defs=k      : type of definition extraction (default is 1)\n");
	printf("                     k = 0 --> no definition extraction.\n");
	printf("                     k = 1 --> only extract definitions that change\n");
	printf("                               quantification level of a variable.\n");
	printf("                     k = 2 --> extract all definitions.\n");
	printf("  -max-confl-min=k : adds conflict minimization directives to modules\n");
	printf("                     0 ... k - 1 (default=2).\n");
	printf("  -max-confl-try=k : maximum number of tries for conflict minimization.\n");
	printf("  -no-simpl        : disables simplification (unit propagation,\n");
	printf("                     equivalence deduction, forced literal detection).\n");
	printf("  -break-sym       : runs external BreakID tool to break symmetries.\n");
	printf("  -bst=<time>      : the maximum amount of time (in seconds) to spend on\n");
	printf("                     breaking symmetries for each level (default=30).\n");
	printf("  -bid=<path>      : gives the path to BreakID tool (defult='./BreakID')\n");
	printf("  -opt-defs        : translate definitions using half of their clauses\n");
	printf("                     whenever possible.\n");
	printf("  -in-format=k     : input format (default is 0)\n");
	printf("                     k = 0 --> QDIMACS format.\n");
	printf("                     k = 1 --> Cleansed Prenex QCIR format.\n");
	printf("  -out-format=k    : output format (default is 0)\n");
	printf("                     k = 0 --> Propagator-based SAT-to-SAT format.\n");
	printf("                     k = 1 --> Module-based SAT-to-SAT format.\n");
	printf("  -h               : shows this help and exits.\n");
}

int main(int argc, char *argv[])
{
	opt_extract_defs = 1;
	opt_optimize_defs = false;
	opt_confl_min_level = 2;
	opt_confl_min_tries = 1;
	opt_sym_breaker_path = new string("./BreakID");
	for (int i = 1; i < argc; i++)
	{
		if (strcmp(argv[i], "-ext-lang") == 0)
			opt_ext_language = true;
		else if (strncmp(argv[i], "-ext-defs=", 10) == 0)
		{
			opt_extract_defs = atoi(argv[i] + 10);
			if ((opt_extract_defs < 0) || (opt_extract_defs > 2))
				fprintf(stderr, "extract definition level can only be 0, 1 or 2.\n"), exit(-1);
		}
		else if (strncmp(argv[i], "-max-confl-min=", 15) == 0)
		{
			opt_confl_min_level = atoi(argv[i] + 15);
			if (opt_confl_min_level < 0)
				fprintf(stderr, "conflict minimization level cannot be less than zero.\n"), exit(-1);
		}
		else if (strncmp(argv[i], "-max-confl-try=", 15) == 0)
		{
			opt_confl_min_tries = atoi(argv[i] + 15);
			if (opt_confl_min_tries < 1)
				fprintf(stderr, "conflict minimization tries cannot be less than 1.\n"), exit(-1);
		}
		else if (strcmp(argv[i], "-opt-defs") == 0)
			opt_optimize_defs = true;
		else if (strcmp(argv[i], "-no-simpl") == 0)
			opt_simplify_db = false;
		else if (strcmp(argv[i], "-break-sym") == 0)
			opt_break_symmetries = true;
		else if (strncmp(argv[i], "-bst=", 5) == 0)
		{
			opt_sym_break_time = atoi(argv[i] + 5);
			if (opt_sym_break_time < 1)
				fprintf(stderr, "symmetry breaking time cannot be less than 1.\n"), exit(-1);
		}
		else if (strncmp(argv[i], "-bid=", 5) == 0)
		{
			delete opt_sym_breaker_path;
			opt_sym_breaker_path = new string(argv[i] + 5);

			struct stat sb;
			if (stat(opt_sym_breaker_path->c_str(), &sb) != 0)
				fprintf(stderr, "given path to symmetry breaking tool is invalid.\n"), exit(-1);
			else
			{
				if ((sb.st_mode & S_IXUSR) == 0)
					fprintf(stderr, "cannot execute the given symmetry breaking tool.\n"), exit(-1);
			}
		}
		else if (strncmp(argv[i], "-in-format=", 11) == 0)
		{
			opt_input_format = atoi(argv[i] + 11);
			if ((opt_input_format < 0) || (opt_input_format > 1))
				fprintf(stderr, "input format can only be 0 or 1.\n"), exit(-1);
		}
		else if (strncmp(argv[i], "-out-format=", 12) == 0)
		{
			opt_output_format = atoi(argv[i] + 12);
			if ((opt_output_format < 0) || (opt_output_format > 1))
				fprintf(stderr, "output format can only be 0 or 1.\n"), exit(-1);
		}
		else if (strcmp(argv[i], "-h") == 0)
			printUsage(), exit(0);
		else
			fprintf(stderr, "Unknown parameter %s.\n", argv[i]), printUsage(), exit(-1);
	}

	QBFProgram *program = readInput(stdin);
	program->quantifyFreeVars();
	//cout << *program;

	if (opt_extract_defs > 0)
		program->extractDefinitions();
	//cout << *program;

	program->simplifyDB();
	//cout << *program;

	if (opt_ext_language)
		program->extendLearningLanguage();
	//cout << *program;

	if (opt_break_symmetries)
		program->breakSymmetries(opt_sym_breaker_path, opt_sym_break_time);
	//cout << *program;

	LayeredQBFProgram *layeredProgram = program->convertToLayeredQBFProgram(0);
	layeredProgram = addExistentialLayer(layeredProgram);
	delete program;
	//cout << *layeredProgram;

	int moduleCount = 0;
	if (opt_output_format == 0)
	{
		STSPropagatorModule *mainModule = (layeredProgram == NULL) ? NULL : layeredProgram->convertToSTSProp(moduleCount);
		//printSTSModule(cout, STYLE_TEXT, mainModule, true);
		printSTSPropagatorModule(cout, STYLE_DIMACS, mainModule, true);
	}
	else
	{
		STSModule *mainModule = (layeredProgram == NULL) ? NULL : layeredProgram->convertToSTS(moduleCount);
		//printSTSModule(cout, STYLE_TEXT, mainModule, true);
		printSTSModule(cout, STYLE_DIMACS, mainModule, true);
	}

	return 0;
}

