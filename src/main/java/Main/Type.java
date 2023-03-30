/*	 Copyright 2016 Hamoon Mousavi
 * 
 * 	 This file is part of Walnut.
 *
 *   Walnut is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   Walnut is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with Walnut.  If not, see <http://www.gnu.org/licenses/>.
*/

package Main;

public enum Type {
	automaton,word,arithmetic,alphabetLetter,variable,numberLiteral;
	public String toString(){
		switch(this){
		case automaton:return "automaton";
		case word:return "word";
		case arithmetic:return "arithmetic";
		case alphabetLetter:return "alphabet letter";
		case variable:return "variable";
		case numberLiteral:return "number literal";
		default:return "unknown";
		}
	}
}
