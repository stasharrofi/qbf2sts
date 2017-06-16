//           io.cc
//  Wed February 17 13:42:13 2016
//  Copyright  2016  Shahab Tasharrofi
//  <shahab.tasharrofi@gmail.com>
// io.cc
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

#include "stdio.h"

#include <algorithm>

#include "io.h"
#include "utils.h"

#define DONT_PRINT_SYMBOL_TABLE

int opt_confl_min_level = 2;
int opt_confl_min_tries = 1;

bool fExpect(FILE *in, const char *s)
{
	while (((*s) != '\0') && (fgetc(in) == *s))
		s++;
	return (*s) == '\0';
}

void fIgnoreWhitespace(FILE *in)
{
	while (!feof(in))
	{
		char c = fgetc(in);
		if ((c != ' ') && (c != '\t') && (c != '\n'))
		{
			ungetc(c, in);
			break;
		}
	}
}

bool fReadInt(FILE *in, int *n)
{
	fIgnoreWhitespace(in);

	if (feof(in))
		return false;

	char c = getc(in);
	bool isNegative = (c == '-');
	if (isNegative)
	{
		if (feof(in))
			return false;
		c = fgetc(in);
	}

	if ((c < '0') || (c > '9'))
		return false;
	(*n) = 0;
	while ((c >= '0') && (c <= '9'))
	{
		int digit = c - '0';
		if (isNegative)
			(*n) = (*n) * 10 - digit;
		else
			(*n) = (*n) * 10 + digit;

		if (feof(in))
			return true;
		c = fgetc(in);
	}

	ungetc(c, in);
	return true;
}

void fIgnoreLine(FILE *in)
{
	while (!feof(in))
		if (fgetc(in) == '\n')
		  break;
}

void parseError(const char *s)
{
	fprintf(stderr, "Parse Error: ");
	fputs(s, stderr);
	fprintf(stderr, "\n");
	exit(-1);
}

QBFProgram *readQDimacs(FILE *in)
{
	int varCount, clauseCount;

	char newChar = fgetc(in);
	while (newChar == 'c')
	{
		fIgnoreLine(in);
		newChar = fgetc(in);
	}
	ungetc(newChar, in);

	if (!fExpect(in, "p cnf "))
		parseError("Expected 'p cnf ' in the beginning of the file!");
	if (!fReadInt(in, &varCount))
		parseError("Expected integer!");
	if (!fReadInt(in, &clauseCount))
		parseError("Expected integer!");
	fIgnoreLine(in);

	QBFProgram *program = new QBFProgram();

	fIgnoreWhitespace(in);
	newChar = fgetc(in);
	while (newChar == 'a' || newChar == 'e' || newChar == 'c')
	{
		if (newChar != 'c')
		{
			program->newQuantifierLevel(newChar == 'a' ? Q_UNIVERSAL : Q_EXISTENTIAL);

			int newVar;
			fReadInt(in, &newVar);
			while (newVar != 0)
			{
				program->addVarToLastQuantifierLevel(Variable::makeVariable(newVar));
				fReadInt(in, &newVar);
			}
		}

		fIgnoreLine(in);
		fIgnoreWhitespace(in);

		newChar = fgetc(in);
	}
	ungetc(newChar, in);

	while (!feof(in))
	{
		newChar = fgetc(in);
		ungetc(newChar, in);
		if (newChar != 'c')
		{
			Clause *clause = new Clause();

			int newLiteral;
			fReadInt(in, &newLiteral);
			while (newLiteral != 0)
			{
				Sign sign = ((newLiteral < 0) ? SGN_NEG : SGN_POS);
				int var = abs(newLiteral);
				clause->push_back(Lit::makeLiteral(Variable::makeVariable(var), sign));
				fReadInt(in, &newLiteral);
			}

			program->addClause(clause);
		}

		fIgnoreLine(in);
		fIgnoreWhitespace(in);
	}

	return program;
}

enum TokenType { TK_Q_UNIV = 0, TK_Q_EXIST = 1, TK_EQ = 2, TK_PAR_OPEN = 3, TK_PAR_CLOSE = 4, TK_COMMA = 5, TK_OUTPUT = 6, TK_G_AND = 7, TK_G_OR = 8, TK_LIT = 9, TK_EOF = 10 };
struct Token { TokenType type; int number; };

Token readToken(FILE *in)
{
	Token token;

	char newChar;
	while (true)
	{
		fIgnoreWhitespace(in);
		if (feof(in))
		{
			token.type = TK_EOF;
			return token;
		}

		newChar = fgetc(in);
		if (newChar == '#')
			fIgnoreLine(in);
		else
			break;
	}

	const char *unknownTokenErrorMessage = "Unkown token.\n";
	switch (newChar)
	{
		case 'f':
			if (feof(in))
				parseError(unknownTokenErrorMessage);
			newChar = fgetc(in);
			if (newChar == 'r')
			{
				if (!fExpect(in, "ee"))
					parseError(unknownTokenErrorMessage);
				token.type = TK_Q_EXIST;
			}
			else if (newChar == 'o')
			{
				if (!fExpect(in, "rall"))
					parseError(unknownTokenErrorMessage);
				token.type = TK_Q_UNIV;
			}
			else
				parseError(unknownTokenErrorMessage);
			break;
		case 'e':
			if (!fExpect(in, "xists"))
				parseError(unknownTokenErrorMessage);
			token.type = TK_Q_EXIST;
			break;
		case '=':
			token.type = TK_EQ;
			break;
		case '(':
			token.type = TK_PAR_OPEN;
			break;
		case ')':
			token.type = TK_PAR_CLOSE;
			break;
		case ',':
			token.type = TK_COMMA;
			break;
		case 'o':
			if (feof(in))
				parseError(unknownTokenErrorMessage);
			newChar = fgetc(in);
			if (newChar == 'u')
			{
				if (!fExpect(in, "tput"))
					parseError(unknownTokenErrorMessage);
				token.type = TK_OUTPUT;
			}
			else if (newChar == 'r')
				token.type = TK_G_OR;
			else
				parseError(unknownTokenErrorMessage);
			break;
		case 'a':
			if (!fExpect(in, "nd"))
				parseError(unknownTokenErrorMessage);
			token.type = TK_G_AND;
			break;
		default:
			if ((newChar != '-') && ((newChar < '0') || (newChar > '9')))
				parseError(unknownTokenErrorMessage);
			ungetc(newChar, in);

			token.type = TK_LIT;
			fReadInt(in, &token.number);
			break;
	}

	return token;
}

void unexpectedTokenError(TokenType expectedToken, TokenType seenToken)
{
	const char *tokenTypeNames[11] = { "'forall'", "'exists'", "'='", "'('", "')'", "','", "'output'", "'and'", "'or'", "[number]", "[eof]" };
	fprintf(stderr, "Parse Error: Expected token %s but seen token %s.\n", tokenTypeNames[expectedToken], tokenTypeNames[seenToken]);
	exit(-1);
}

void expectToken(FILE *in, TokenType expectedTokenType)
{
	Token seenToken = readToken(in);
	if (seenToken.type != expectedTokenType)
		unexpectedTokenError(expectedTokenType, seenToken.type);
}

void readParameters(FILE *in, vector<Lit> &lits)
{
	expectToken(in, TK_PAR_OPEN);

	lits.clear();
	Token token = readToken(in);
	while (token.type == TK_LIT)
	{
		if (token.number == 0)
			parseError("Literal or variable is zero.");
		lits.push_back(Lit::makeLiteral(Variable::makeVariable(abs(token.number)), (token.number < 0) ? SGN_NEG : SGN_POS));

		token = readToken(in);
		if (token.type == TK_COMMA)
			token = readToken(in);
	}
	if (token.type != TK_PAR_CLOSE)
		unexpectedTokenError(TK_PAR_CLOSE, token.type);
}

QBFProgram *readPrenexQCIR(FILE *in)
{
	QBFProgram *program = new QBFProgram();

	vector<Lit> lits;
	Token token = readToken(in);
	while (token.type == TK_Q_UNIV || token.type == TK_Q_EXIST)
	{
		program->newQuantifierLevel((token.type == TK_Q_UNIV) ? Q_UNIVERSAL : Q_EXISTENTIAL);

		readParameters(in, lits);
		for (auto it = lits.cbegin(); it != lits.cend(); it++)
			if (it->sign == SGN_NEG)
			  parseError("Found negative quantified variable.\n");
			else
				program->addVarToLastQuantifierLevel(it->var);

		token = readToken(in);
	}

	if (token.type != TK_OUTPUT)
		unexpectedTokenError(TK_OUTPUT, token.type);
	readParameters(in, lits);
	if (lits.size() != 1)
		parseError("Output keyword should contain exactly one literal.");
	program->addClause(new Clause(lits));

	token = readToken(in);
	while (token.type != TK_EOF)
	{
		if (token.type != TK_LIT)
			unexpectedTokenError(TK_LIT, token.type);
		if (token.number <= 0)
			parseError("Gate output should be a variable and not a literal.");
		Variable var = Variable::makeVariable(token.number);

		expectToken(in, TK_EQ);
		token = readToken(in);
		if ((token.type != TK_G_AND) && (token.type != TK_G_OR))
			parseError("Expected either 'and' or 'or' gate.");

		Lit outputLiteral = Lit::makeLiteral(var, (token.type == TK_G_AND) ? SGN_NEG : SGN_POS);
		readParameters(in, lits);
		if (token.type == TK_G_OR)
		{
			for (int i = 0; i < lits.size(); i++)
				lits[i] = lits[i].negated();
		}
		program->addDefinition(new Definition(outputLiteral, lits));

		token = readToken(in);
	}

	return program;
}

void printClauseDictionary(std::ostream& os, int tab, ClauseDictionary *node)
{
	if (node == NULL)
	{
		os << "NULL" << endl;
		return;
	}

	os << endl;

	printTabs(os, tab);
	os << "[var : " << node->var << ", location : " << node->location << endl;

	printTabs(os, tab);
	os << "pos --> ";
	printClauseDictionary(os, tab + 1, node->positiveAppearences);

	printTabs(os, tab);
	os << "neg --> ";
	printClauseDictionary(os, tab + 1, node->negativeAppearences);

	printTabs(os, tab);
	os << "non --> ";
	printClauseDictionary(os, tab + 1, node->nonAppearences);
}

std::ostream& operator<<(std::ostream& os, const ClauseIndexVector &clauseIndices)
{
	for (int i = 0; i < clauseIndices.clausesByMinVar.size(); i++)
	{
		os << "[" << i << "] ";
		printClauseDictionary(os, 1, clauseIndices.clausesByMinVar[i]);
	}

	return os;
}

void printSTSPropagatorModule(std::ostream& os, OutputStyle style, STSPropagatorModule *module, bool topModule)
{
	if (style == STYLE_TEXT)
	{
		for (int i = 0; i < module->negativeSubmodules.size(); i++)
			printSTSPropagatorModule(os, style, module->negativeSubmodules[i]->submodule, false);

		os << "###### MODULE " << module->moduleNo << " ######" << endl;
		os << "Total variables: " << module->variableCount << endl;

		os << "Positive Dictionary: ";
		for (auto it = module->positiveDictionary.cbegin(); it != module->positiveDictionary.cend(); it++)
			os << it->first << "->" << it->second << " ";
		os << endl;

		os << "Negative Dictionary: ";
		for (auto it = module->negativeDictionary.cbegin(); it != module->negativeDictionary.cend(); it++)
			os << it->first << "->" << it->second << " ";
		os << endl;

		os << "Internal Dictionary: ";
		for (auto it = module->internalDictionary.cbegin(); it != module->internalDictionary.cend(); it++)
			os << it->first << "->" << it->second << " ";
		os << endl;

		os << "Positive Input Variables: ";
		for (int i = 0; i < module->positiveInputVariables.size(); i++)
			os << module->positiveInputVariables[i] << " ";
		os << "0" << endl;

		os << "Negative Input Variables: ";
		for (int i = 0; i < module->negativeInputVariables.size(); i++)
			os << module->negativeInputVariables[i] << " ";
		os << "0" << endl;

		for (int i = 0; i < module->negativeSubmodules.size(); i++)
		{
			NegativePropagatorSubmodule *negSubmodule = module->negativeSubmodules[i];
			os << "Uses submodule " << negSubmodule->submodule->moduleNo << " negatively:" << endl;

			os << "  positive variable bindings: ";
			for (int j = 0; j < negSubmodule->positiveBindings.size(); j++)
				os << negSubmodule->positiveBindings[j] << " ";
			os << "0" << endl;

			os << "  negative variable bindings: ";
			for (int j = 0; j < negSubmodule->negativeBindings.size(); j++)
				os << negSubmodule->negativeBindings[j] << " ";
			os << "0" << endl;
		}

		for (int i = 0; i < module->clauses.size(); i++)
			os << "clause " << *(module->clauses[i]) << endl;

		os << "###### END MODULE " << module->moduleNo << " ######" << endl;
	}
	else if (style == STYLE_DIMACS)
	{
		if (topModule)
			os << "p cnf " << module->variableCount << " " << module->clauses.size() << endl;

		for (int i = 0; i < module->negativeSubmodules.size(); i++)
		{
			NegativePropagatorSubmodule *negSubmodule = module->negativeSubmodules[i];
			os << "c propagator " << negSubmodule->submodule->variableCount << " 1 " << negSubmodule->negativeBindings.size();
			for (int j = 0; j < negSubmodule->negativeBindings.size(); j++)
				os << " " << negSubmodule->negativeBindings[j] << " " << negSubmodule->submodule->negativeInputVariables[j];

			os << " " << negSubmodule->positiveBindings.size();
			for (int j = 0; j < negSubmodule->positiveBindings.size(); j++)
				os << " " << negSubmodule->positiveBindings[j] << " " << negSubmodule->submodule->positiveInputVariables[j];

			os << " 0" << endl;
			printSTSPropagatorModule(os, style, module->negativeSubmodules[i]->submodule, false);
			os << "c endpropagator" << endl;
		}

#ifdef PRINT_SYMBOL_TABLE
		for (auto it = module->positiveDictionary.cbegin(); it != module->positiveDictionary.cend(); it++)
			os << "c " << it->first << " p" << it->second << " " << endl;
		for (auto it = module->negativeDictionary.cbegin(); it != module->negativeDictionary.cend(); it++)
			os << "c " << it->first << " n" << it->second << " " << endl;
		for (auto it = module->internalDictionary.cbegin(); it != module->internalDictionary.cend(); it++)
			os << "c " << it->first << " i" << it->second << " " << endl;
#endif

		for (int i = 0; i < module->clauses.size(); i++)
			os << *(module->clauses[i]) << endl;
	}
	else
		fprintf(stderr, "Unknown output style.\n"), exit(-1);
}

void printSTSModule(std::ostream& os, OutputStyle style, STSModule *module, bool topModule)
{
	if (style == STYLE_TEXT)
	{
		for (int i = 0; i < module->negativeSubmodules.size(); i++)
			printSTSModule(os, style, module->negativeSubmodules[i]->submodule, false);

		os << "###### MODULE " << module->moduleNo << " ######" << endl;
		os << "Total variables: " << module->variableCount << endl;

		os << "External Dictionary: ";
		for (auto it = module->externalDictionary.cbegin(); it != module->externalDictionary.cend(); it++)
			os << it->first << "->" << it->second << " ";
		os << endl;

		os << "Internal Dictionary: ";
		for (auto it = module->internalDictionary.cbegin(); it != module->internalDictionary.cend(); it++)
			os << it->first << "->" << it->second << " ";
		os << endl;

		os << "Input Variables: ";
		for (int i = 0; i < module->inputVariables.size(); i++)
			os << module->inputVariables[i].first << " ";
		os << "0" << endl;

		for (int i = 0; i < module->negativeSubmodules.size(); i++)
		{
			NegativeSubmodule *negSubmodule = module->negativeSubmodules[i];
			os << "Uses submodule " << negSubmodule->submodule->moduleNo << " negatively:" << endl;

			os << "  variable bindings: ";
			for (int j = 0; j < negSubmodule->bindings.size(); j++)
				os << negSubmodule->bindings[j] << " ";
			os << "0" << endl;
		}

		for (int i = 0; i < module->clauses.size(); i++)
			os << "clause " << *(module->clauses[i]) << endl;

		os << "###### END MODULE " << module->moduleNo << " ######" << endl;
	}
	else if (style == STYLE_DIMACS)
	{
		if (topModule)
			os << "p cnf " << module->variableCount << " " << module->clauses.size() << endl;

		for (int i = 0; i < module->negativeSubmodules.size(); i++)
			printSTSModule(os, style, module->negativeSubmodules[i]->submodule, false);

		if (!topModule)
		{
			os << "module " << module->variableCount << " " << module->inputVariables.size();
			for (int i = 0; i < module->inputVariables.size(); i++)
				os << " " << module->inputVariables[i].first;
			os << endl;
			if (module->moduleNo < opt_confl_min_level)
				os << "c config -max-confl-try=" << opt_confl_min_tries << endl;
		}

		for (int i = 0; i < module->clauses.size(); i++)
			os << *(module->clauses[i]) << endl;

		for (int i = 0; i < module->negativeSubmodules.size(); i++)
		{
			NegativeSubmodule *negSubmodule = module->negativeSubmodules[i];
			os << "falsify " << negSubmodule->submodule->moduleNo;
			for (int j = 0; j < negSubmodule->bindings.size(); j++)
				os << " " << negSubmodule->bindings[j];
			os << endl;
		}

#ifdef PRINT_SYMBOL_TABLE
		for (auto it = module->externalDictionary.cbegin(); it != module->externalDictionary.cend(); it++)
			os << "c " << it->first << " e" << it->second << " " << endl;
		for (auto it = module->internalDictionary.cbegin(); it != module->internalDictionary.cend(); it++)
			os << "c " << it->first << " i" << it->second << " " << endl;
#endif

		if (!topModule)
			os << "endmodule" << endl;
	}
	else
		fprintf(stderr, "Unknown output style.\n"), exit(-1);
}

