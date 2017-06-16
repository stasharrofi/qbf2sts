//           utils.cxx
//  Thu February 18 15:47:42 2016
//  Copyright  2016  Shahab Tasharrofi
//  <shahab.tasharrofi@gmail.com>
// utils.cxx
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

#include "utils.h"

void printTabs(std::ostream& os, int tabs)
{
	for (int i = 0; i < tabs; i++)
		os << "  ";
}

