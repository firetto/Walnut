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
import java.util.HashSet;
import java.util.Stack;

import Main.Expression;
import Automata.Automaton;
import Automata.NumberSystem;
import Main.Type;
import Main.UtilityMethods;


public class ArithmeticOperator extends Operator{
	NumberSystem number_system;
	public ArithmeticOperator(int position,String op, NumberSystem number_system) throws Exception{
		this.op = op;
		setPriority();
		if (op.equals("_")) {
			setArity(1);
		} else {
			setArity(2);
		}
		setPositionInPredicate(position);
		this.number_system = number_system;
	}
	public String toString(){
		return op+"_"+number_system;
	}
	public void act(Stack<Expression> S,boolean print,String prefix,StringBuffer log) throws Exception{
		if(S.size() < getArity())throw new Exception("operator " + op + " requires " + getArity()+ " operands");
		Expression b = S.pop();
		if(!(b.is(Type.alphabetLetter) || b.is(Type.word) || b.is(Type.arithmetic) || b.is(Type.variable) || b.is(Type.numberLiteral)))
			throw new Exception("operator " + op + " cannot be applied to the operand " +b+" of type " + b.getType());

		if(op.equals("_")) {
			if(b.is(Type.numberLiteral)) {
				S.push(new Expression(Integer.toString(-b.constant), -b.constant, number_system));
				return;
			} else if(b.is(Type.alphabetLetter)) {
				S.push(new Expression("@"+(-b.constant), -b.constant));
				return;
			} else if(b.is(Type.word)) {
				b.W.applyOperator(0,"_", print, prefix, log);
				S.push(b);
				return;
			}
			String c = getUniqueString();
			// b + c = 0
			Automaton M = number_system.arithmetic(b.identifier,c,0,"+");
			String preStep = prefix + "computing " + op+b;
			log.append(preStep + UtilityMethods.newLine());
			if(print){
				System.out.println(preStep);
			}
			if(b.is(Type.arithmetic)){
				// Eb, b + c = 0 & M(b,...)
				M = M.and(b.M,print,prefix+" ",log);
				M.quantify(b.identifier,print,prefix+" ",log);
			}
			S.push(new Expression("("+op+b+")",M,c));
			String postStep = prefix + "computed " + op+b;
			log.append(postStep + UtilityMethods.newLine());
			if(print){
				System.out.println(postStep);
			}
			return;
		}

		Expression a = S.pop();
		if(!(a.is(Type.alphabetLetter) || a.is(Type.word) || a.is(Type.arithmetic) || a.is(Type.variable) || a.is(Type.numberLiteral)))
			throw new Exception("operator " + op + " cannot be applied to the operand "+ a+ " of type " + a.getType());

		if(a.is(Type.word) && b.is(Type.word)) {
			a.W = a.W.applyOperator(b.W, op, print, prefix, log);
			a.M = a.M.and(b.M, print, prefix+" ", log);
			a.list_of_identifiers_to_quantify.addAll(b.list_of_identifiers_to_quantify);
			S.push(a);
			return;
		}
		if(a.is(Type.word) && (b.is(Type.alphabetLetter) || b.is(Type.numberLiteral))) {
			a.W.applyOperator(op, b.constant, print, prefix, log);
			S.push(a);
			return;
		}
		if((a.is(Type.alphabetLetter) || a.is(Type.numberLiteral)) && b.is(Type.word)) {
			b.W.applyOperator(a.constant, op, print, prefix, log);
			S.push(b);
			return;
		}

		if((a.is(Type.numberLiteral) || a.is(Type.alphabetLetter)) && (b.is(Type.numberLiteral) || b.is(Type.numberLiteral))) {
			switch (op) {
				case "+":
					S.push(new Expression(Integer.toString(a.constant + b.constant), a.constant + b.constant, number_system));
					return;
				case "*":
					S.push(new Expression(Integer.toString(a.constant * b.constant), a.constant * b.constant, number_system));
					return;
				case "/":
					int c = Math.floorDiv(a.constant, b.constant);
					S.push(new Expression(Integer.toString(c), c, number_system));
					return;
				case "-":
					S.push(new Expression(Integer.toString(a.constant - b.constant), a.constant - b.constant, number_system));
					return;
			}
		}
		String c = getUniqueString();
		Automaton M;
		String preStep = prefix + "Computing " + a+op+b;
		log.append(preStep + UtilityMethods.newLine());
		if(print){
			System.out.println(preStep);
		}
		if( (a.is(Type.word) && (b.is(Type.arithmetic) || b.is(Type.variable))) ||
				((a.is(Type.arithmetic) || a.is(Type.variable)) && b.is(Type.word)) ) {
			/* We rewrite T[a] * 5 = z as
			 * (T[a] = @0 => 0 * 5 = z) & (T[a] = @1 => 1 * 5 = z)
			 * With more statements of the form (T[a] = @i => i * 5 = z) for each output i.
			 */
			Expression word; Expression arithmetic; boolean reverse;
			if(a.is(Type.word)) {
				word = a;
				arithmetic = b;
				reverse = false;
			} else {
				word = b;
				arithmetic = a;
				reverse = true;
			}

			M = new Automaton(true);
			for(int o : word.W.O) {
				Automaton N = word.W.clone();
				N.compare(o, "=",print,prefix+" ",log);
				Automaton C;
				if(o == 0 && op.equals("*")){
					C = number_system.get(0);
					C.bind(c);
				} else if (reverse) {
					C = number_system.arithmetic(arithmetic.identifier, o, c, op);
				} else {
					C = number_system.arithmetic(o, arithmetic.identifier,c, op);
				}
				N = N.imply(C, print, prefix+" ",log);
				M = M.and(N,print,prefix+" ",log);
			}
			M = M.and(word.M,print,prefix+" ",log);
			M.quantify(new HashSet<>(word.list_of_identifiers_to_quantify),print,prefix+" ",log);
			if(arithmetic.is(Type.arithmetic)){
				M = M.and(arithmetic.M,print,prefix+" ",log);
				M.quantify(arithmetic.identifier,print,prefix+" ",log);
			}
		} else {
			if(a.is(Type.numberLiteral)){
				if(a.constant == 0 && op.equals("*")){
					S.push(new Expression("0",0,number_system));
					return;
				}
				else
					M = number_system.arithmetic(a.constant, b.identifier, c, op);
			}
			else if(b.is(Type.numberLiteral)){
				if(b.constant == 0 && op.equals("*")){
					S.push(new Expression("0",0,number_system));
					return;
				}
				M = number_system.arithmetic(a.identifier, b.constant, c, op);
			}
			else{
				M = number_system.arithmetic(a.identifier, b.identifier, c, op);
			}

			if(a.is(Type.arithmetic)){
				M = M.and(a.M,print,prefix+" ",log);
				M.quantify(a.identifier,print,prefix+" ",log);
			}
			if(b.is(Type.arithmetic)){
				M = M.and(b.M,print,prefix+" ",log);
				M.quantify(b.identifier,print,prefix+" ",log);
			}
		}
		S.push(new Expression("("+a+op+b+")",M,c));
		String postStep = prefix + "computed " + a+op+b;
		log.append(postStep + UtilityMethods.newLine());
		if(print){
			System.out.println(postStep);
		}
	}
}
