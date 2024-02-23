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


public abstract class Operator extends Token{
	protected boolean leftParenthesis = false;
	int priority;
	protected String op;
	public boolean isOperator(){
		return true;
	}
	public void put(List<Token> postOrder,Stack<Operator> S)throws Exception{
		if(op.equals("(") || op.equals("E") || op.equals("A") || op.equals("I")){
			S.push(this);
			return;
		}
		while(!S.isEmpty()){
			if(S.peek().getPriority() <= this.getPriority()){
				if( rightAssociativity() && S.peek().getPriority() == this.getPriority() ){
					break;
				}
				Operator op = S.pop();
				postOrder.add(op);
			}
			else{
				break;
			}
		}
		S.push(this);
	}
	public String toString(){
		return op;
	}
	public boolean isLeftParenthesis(){return leftParenthesis;}
	public boolean rightAssociativity(){
		if(op.equals("`") || this.isNegation(op))
			return true;
		return false;
	}
	public void setPriority(){
		switch(op){
			case "_":priority = 5;break;
			case "*":priority = 10;break;
			case "/":priority = 10;break;
			case "+":priority = 20;break;
			case "-":priority = 20;break;
			case "=":priority = 40;break;
			case "!=":priority = 40;break;
			case "<":priority = 40;break;
			case ">":priority = 40;break;
			case "<=":priority = 40;break;
			case ">=":priority = 40;break;
			case "~":priority = 80;break;
			case "`":priority = 80;break;
			case "&":priority = 90;break;
			case "|":priority = 90;break;
			case "^":priority = 90;break;
			case "=>":priority = 100;break;
			case "<=>":priority = 110;break;
			case "E":priority = 150;break;
			case "A":priority = 150;break;
			case "I":priority = 150;break;
			case "(":priority = 200;break;
			default:
				if (this.isNegation(op)) {
					priority = 80;
				}
				else {
					priority = Integer.MAX_VALUE;
				}
		}
	}
	public int getPriority(){return priority;}

	/*
	To allow for multiple kinds of tildes (~, ˜,  ̃), this function needs to be run instead of directly comparing the
	character with the usual ~ tilde.
	This function allows for the \u02dc tilde and \u0303 tilde.
	 */
	public boolean isNegation(String op) {
		boolean specialNegation = false;

		if (op.length() == 1) {
			String hexString = Integer.toHexString((int) op.charAt(0));
			// check if the string has unicode code 2dc or 303. different types of tildes.
			specialNegation = hexString.equals("2dc") || hexString.equals("303");
		}

		return specialNegation || op.equals("~");
	}
}
