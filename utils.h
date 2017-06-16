/***************************************************************************
 *            utils.h
 *
 *  Thu February 18 15:47:42 2016
 *  Copyright  2016  Shahab Tasharrofi
 *  <shahab.tasharrofi@gmail.com>
 ****************************************************************************/
/*
 * utils.h
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

#ifndef _UTILS_H
#define _UTILS_H

#include <iostream>

void printTabs(std::ostream& os, int tabs);
inline int max(int a, int b) { return (a < b) ? b : a; }

#endif