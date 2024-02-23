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

import java.util.List;

import Automata.Automaton;
import Automata.NumberSystem;
/**
 * Examples of expression: a,a+b, a+b > 2,c=a+b, W[a]!=W[b], Ea W[a]!=W[a+1],...<br>
 * Some expressions evaluate to automaton. For example a+b>2 is an expression, and its value is an automaton with two
 * inputs which accepts only if the sum of two inputs is greater than 2.<br>
 * Here is the list of all different types of expressions:<br>
 * -alphabetLetter: an integer that follows @ in the predicate is an alphabetLetter expression. It evaluates to the integer
 * that follows @. For example W[a] = @-1 has the alphabetLetter expression @-1 which evaluates to -1. We store the value
 * of an alphabetLetter expression in the field member constant.<br>
 * -numberLiteral: any positive integer that is not an alphabetLetter is a numberLiteral expression. For example in the expression
 * a+2 = b the integer 2 is a numberLiteral expression. The value of a numberLiteral expression is the positive integer itself, and 
 * we store it in the field member constant (like we did for alphabetLetter expression), but we also need to store
 * the number system in which the constant belongs to. We store the number system in the field member base.<br>
 * -variable: for example in the expression a+2=b, a and b are variables. The value of a variable is its name, and we store
 * it in the field member identifier. <br>
 * -arithmetic: arithmetic expression is an expression with arithmetic operators: +,-,*,/. It has to have at
 * least one operator in it and no operators of other types. For example a+b is an arithmetic expression but a is not. Also note that c=a+b is not arithmetic, since
 * = is not an arithmetic operator but a comparison operator. An arithmetic expression evaluates to
 * an automaton, stored in the field memeber M, and an identifier, stored in identifier. For example a+b-c*2, evaluates
 * to an automaton with 4 inputs a,b,c,x and it accepts iff x = a+b-c*2. This x is a unique identifier we generate for this expression.
 * As we mentioned earlier, we store the automaton in M and the x in identifier since we need to eliminate x in future.<br>
 * -automaton: automaton is an expression with at least one of reverse, logical, or comparison operator: 
 * &(and),|(or),^(xor),~(not),`(reverse),E(existential quantifier),A(universal quantifier),=,!=,<,>,<=,>=<br>
 * For example a+b > c is an automaton expression, so it `$f(a,b+1). An automaton expression, evaluates to an automaton.
 * For example a+b>c evaluates to an automaton with three inputs a,b, and c, and accepts iff a+b>c. <br>
 * -word: a word is an expression that has a list of [] followed by the name of the word. For example: Thue[a+b],
 * PaperFolding[f][x+1], Fibonacci[n], .... A word is evaluated to two automata which are stored in W and M. But why two?
 * Take the word expression Thue[a+b*2 - c]: We store in W the automaton for Thue[x], where x is 
 * a variable we generate, but we also need to store the
 * arithmetic expression a+b*2-c. So we store the automaton expression x=a+b*2-c in M.
 * We also need to store x since we need to eliminate it in future using quantification. We store the list of variables to quantify in the member field list_of_identifiers_to_quantify  <br>
 * Note that Thue[a] != Thue[b] is an automaton expression and not a word expression.
 * @author Hamoon
 *
 */		
public class Expression {
	/**
	 * The string that represent the expression
	 */
	String expressionInString;
	public Automaton M;
	public String identifier;
	public int constant;
	public NumberSystem base;
	public Automaton W;
	public List<String> list_of_identifiers_to_quantify;
	/**
	 * Different types: automaton,word,arithmetic,alphabetLetter,variable,numberLiteral
	 */
	public Type T;
	public Expression(String identifier){
		this.identifier = identifier;
		this.expressionInString = identifier;
		T = Type.variable;
	}
	
	public Expression(String expressionInString, int value) throws Exception{
		this.expressionInString = expressionInString;
		this.constant = value;
		T = Type.alphabetLetter;
	}
	public Expression(String expressionInString, int value,NumberSystem base) throws Exception{
		this.expressionInString = expressionInString;
		this.constant = value;
		this.base = base;
		T = Type.numberLiteral;
	}
	public Expression(String expressionInString,Automaton M){
		this.expressionInString = expressionInString;
		this.M = M;
		T = Type.automaton;
	}
	public Expression(String expressionInString,Automaton M,String identifier){
		this.expressionInString = expressionInString;
		this.M = M;
		this.identifier = identifier;
		T = Type.arithmetic;
	}
	public Expression(String expressionInString,Automaton W,Automaton M,List<String> quantify){
		this.expressionInString = expressionInString;
		this.W = W;
		this.M = M;
		list_of_identifiers_to_quantify = quantify;
		T = Type.word;
	}
	
	public String toString(){
		return expressionInString;
	}
	public boolean is(Type T){
		return this.T == T;
	}
	public Type getType(){
		return T;
	}
}
