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

package Token;

import java.util.List;
import java.util.Stack;

import Main.Expression;

public abstract class Token {
	int arity;
	int positionInPredicate;
	static char uniqueChar = 1000;
	/**
	 * 
	 * @return a string. It is gauranteed that the string does not have ascii characters, and that no two calls
	 * return the same value.
	 */
	protected String getUniqueString(){
		uniqueChar++;
		return Character.toString(uniqueChar);
	}
	public void put(List<Token> postOrder){
		postOrder.add(this);
	}

	public abstract void act(Stack<Expression> S,boolean print,String prefix,StringBuffer log) throws Exception;
	public boolean isOperator(){
		return false;
	}
	public int getPositionInPredicate(){return positionInPredicate;}
	public int getArity(){return arity;}
	public void setArity(int arity){this.arity = arity;}
	public void setPositionInPredicate(int positionInPredicate){this.positionInPredicate = positionInPredicate;}
}