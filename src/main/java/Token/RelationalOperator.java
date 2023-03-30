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
import Main.Expression;
import Automata.Automaton;
import Automata.NumberSystem;
import Main.Type;
import Main.UtilityMethods;

import java.util.HashSet;
import java.util.Stack;


public class RelationalOperator extends Operator{
	NumberSystem number_system;
	public RelationalOperator(int position,String type, NumberSystem number_system) throws Exception{
		this.op = type;
		setPriority();
		setArity(2);
		setPositionInPredicate(position);
		this.number_system = number_system;
	}
	public String toString(){
		return op+"_"+number_system;
	}
	public void act(Stack<Expression> S,boolean print,String prefix,StringBuffer log) throws Exception{

		if(S.size() < getArity())throw new Exception("operator " + op + " requires " + getArity()+ " operands");
		Expression b = S.pop();
		Expression a = S.pop();
		
		if((a.is(Type.numberLiteral) || a.is(Type.alphabetLetter)) && (b.is(Type.numberLiteral) || b.is(Type.alphabetLetter))){
			S.push(new Expression(a+op+b,new Automaton(compare(a.constant,b.constant))));
			return;
		}
		String preStep = prefix + "computing " + a+op+b;
		log.append(preStep + UtilityMethods.newLine());
		if(print) {
			System.out.println(preStep);
		}
		if( (a.is(Type.word) && (b.is(Type.arithmetic) || b.is(Type.variable))) ||
				((a.is(Type.arithmetic) || a.is(Type.variable)) && b.is(Type.word)) ) {
			/* We rewrite T[a] < b as
			 * (T[a] = @0 => 0 < b) & (T[a] = @1 => 1 < b)
			 * With more statements of the form (T[a] = @i => i < b) for each output i.
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

			Automaton M = new Automaton(true);
			for(int o : word.W.O) {
				Automaton N = word.W.clone();
				N.compare(o, "=",print,prefix+" ",log);
				Automaton C;
				if (reverse) {
					C = number_system.comparison(arithmetic.identifier, o, op);
				} else {
					C = number_system.comparison(o, arithmetic.identifier, op);
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
			S.push(new Expression(word.toString(), M));
		}
		else if((a.is(Type.arithmetic) || a.is(Type.variable))
				&& (b.is(Type.arithmetic) || b.is(Type.variable))){
			Automaton M = number_system.comparison(a.identifier, b.identifier, op);
			if(a.is(Type.arithmetic)){
				M = M.and(a.M,print,prefix+" ",log);
				M.quantify(a.identifier,print,prefix+" ",log);
			}
			if(b.is(Type.arithmetic)){
				M = M.and(b.M,print,prefix+" ",log);
				M.quantify(b.identifier,print,prefix+" ",log);
			}
			
			S.push(new Expression(a+op+b,M));
		}
		else if((a.is(Type.numberLiteral) || a.is(Type.alphabetLetter)) && (b.is(Type.arithmetic) || b.is(Type.variable))){
			Automaton M = number_system.comparison(a.constant, b.identifier, op);
			if(b.is(Type.arithmetic)){
				M = M.and(b.M,print,prefix+" ",log);
				M.quantify(b.identifier,print,prefix+" ",log);
			}
			S.push(new Expression(a+op+b,M));
		}
		else if((a.is(Type.arithmetic) || a.is(Type.variable)) && (b.is(Type.numberLiteral) || b.is(Type.alphabetLetter))){
			Automaton M = number_system.comparison(a.identifier, b.constant, op);
			if(a.is(Type.arithmetic)){
				M = M.and(a.M,print,prefix+" ",log);
				M.quantify(a.identifier,print,prefix+" ",log);
			}	
			S.push(new Expression(a+op+b,M));
		}
		else if(a.is(Type.word) && b.is(Type.word)){
			Automaton M = a.W.compare(b.W, op,print,prefix+" ",log);
			M = M.and(a.M,print,prefix+" ",log);
			M = M.and(b.M,print,prefix+" ",log);
			M.quantify(new HashSet<>(a.list_of_identifiers_to_quantify),print,prefix+" ",log);
			M.quantify(new HashSet<>(b.list_of_identifiers_to_quantify),print,prefix+" ",log);
			S.push(new Expression(a+op+b,M));
		}
		else if(a.is(Type.word) && (b.is(Type.numberLiteral) || b.is(Type.alphabetLetter))){
			a.W.compare(b.constant, op,print,prefix+" ",log);
			Automaton M = a.W;
			M = M.and(a.M,print,prefix+" ",log);
			M.quantify(new HashSet<String>(a.list_of_identifiers_to_quantify),print,prefix+" ",log);
			S.push(new Expression(a+op+b,M));
		}
		else if((a.is(Type.numberLiteral) || a.is(Type.alphabetLetter)) && b.is(Type.word)){
			b.W.compare(a.constant, reverseOperator(op),print,prefix+" ",log);
			Automaton M = b.W;
			M = M.and(b.M,print,prefix+" ",log);
			M.quantify(new HashSet<String>(b.list_of_identifiers_to_quantify),print,prefix+" ",log);
			S.push(new Expression(a+op+b,M));
		}
		else{
			throw new Exception("operator " + op + " cannot be applied to operands "+a+" and " +b+ " of types " + a.getType() +" and " + b.getType() + " respectively");
		}	
		String postStep = prefix + "computed " + a+op+b;  
		log.append(postStep + UtilityMethods.newLine());
		if(print){
			System.out.println(postStep);
		}
	}
	private boolean compare(int a,int b){
		switch(op){
		case "=":return a == b;
		case "!=":return a != b;
		case "<":return a <b;
		case ">":return a>b;
		case "<=":return a<=b;
		case ">=":return a>=b;
		default:
			return false;
		}
		
	}
	public String reverseOperator(String a){
		switch(op){
		case "=":return "=";
		case "!=":return "!=";
		case "<":return ">";
		case ">":return "<";
		case "<=":return ">=";
		case ">=":return "<=";
		default:
			return "";
		}
	}
}
