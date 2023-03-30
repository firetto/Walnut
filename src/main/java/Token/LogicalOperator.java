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
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Stack;

import Main.Expression;
import Automata.Automaton;
import Main.Type;
import Main.UtilityMethods;

public class LogicalOperator extends Operator{
	int number_of_quantified_variables;
	public LogicalOperator(int position,String op) throws Exception{
		this.op = op;
		setPriority();




		if(this.isNegation(op) || op.equals("`")) setArity(1);
		else setArity(2);
		setPositionInPredicate(position);
	}
	public LogicalOperator(int position,String op,int number_of_quantified_variables) throws Exception{
		this.number_of_quantified_variables = number_of_quantified_variables;
		this.op = op;

		setPriority();
		setArity(number_of_quantified_variables+1);
		setPositionInPredicate(position);
	}

	public void act(Stack<Expression> S,boolean print,String prefix,StringBuffer log) throws Exception{
		if(S.size() < getArity())throw new Exception("operator " + op + " requires " + getArity()+ " operands");
		
		if(this.isNegation(op) || op.equals("`")){
			actNegationOrReverse(S,print,prefix,log);
			return;
		}
		if(op.equals("E") || op.equals("A") || op.equals("I")){actQuantifier(S,print,prefix,log);return;}
		
		Expression b = S.pop();
		Expression a = S.pop();
		
		if(a.is(Type.automaton) && b.is(Type.automaton)){
			String preStep = prefix + "computing "+a+op+b;  
			log.append(preStep + UtilityMethods.newLine());
			if(print){
				System.out.println(preStep);
			}
			switch(op){
				case "&":S.push(new Expression("("+a+op+b+")",a.M.and(b.M,print,prefix+" ",log)));break;
				case "|":S.push(new Expression("("+a+op+b+")",a.M.or(b.M,print,prefix+" ",log)));break;
				case "^":S.push(new Expression("("+a+op+b+")",a.M.xor(b.M,print,prefix+" ",log)));break;
				case "=>":S.push(new Expression("("+a+op+b+")",a.M.imply(b.M,print,prefix+" ",log)));break;
				case "<=>":S.push(new Expression("("+a+op+b+")",a.M.iff(b.M,print,prefix+" ",log)));break;
			}
			String postStep = prefix + "computed "+a+op+b;  
			log.append(postStep + UtilityMethods.newLine());
			if(print){
				System.out.println(postStep);
			}
			return;
		}	
		throw new Exception("operator " + op + " cannot be applied to operands "+a +" and "+b +" of types " + a.getType() +" and " + b.getType() + " respectively");
			
	}
	private void actNegationOrReverse(Stack<Expression> S,boolean print,String prefix,StringBuffer log) throws Exception{
		Expression a = S.pop();
		if(a.is(Type.automaton)){
			String preStep = prefix + "computing "+op + a;
			log.append(preStep + UtilityMethods.newLine());
			if(print){
				System.out.println(preStep);
			}
			if(op.equals("`"))
				a.M.reverse(print, prefix+" ", log, true);
			if(this.isNegation(op))
				a.M.not(print,prefix+" ",log);
			S.push(new Expression(op + a,a.M));
			String postStep = prefix + "computed "+op+a;
			log.append(postStep + UtilityMethods.newLine());
			if(print){
				System.out.println(postStep);
			}
			return;
		}
		throw new Exception("operator " + op + " cannot be applied to the operand "+a +" of type " + a.getType());
	}
	private void actQuantifier(Stack<Expression> S,boolean print,String prefix,StringBuffer log) throws Exception{
		String stringValue = "("+op + " ";
		Stack<Expression> temp = new Stack<Expression>();
		List<Expression> operands = new ArrayList<Expression>();
		Automaton M = null;
		for(int i = 0; i < getArity();i++){
			temp.push(S.pop());
		}
		String preStep = prefix + "computing quantifier "+op;  
		log.append(preStep + UtilityMethods.newLine());
		if(print){
			System.out.println(preStep);
		}
		List<String> list_of_identifiers_to_quantify = new ArrayList<String>();
		for(int i = 0 ; i < getArity();i++){
			operands.add(temp.pop());
			if(i < getArity()-1){
				if(i == 0)
					stringValue += operands.get(i)+" ";
				else
					stringValue += ", "+operands.get(i)+" ";
				if(!operands.get(i).is(Type.variable))
					throw new Exception("operator " + op + " requires a list of "+number_of_quantified_variables + " variables");
				
				list_of_identifiers_to_quantify.add(operands.get(i).identifier);
			}
			else if(i == getArity()-1){
				stringValue += operands.get(i);
				if(!operands.get(i).is(Type.automaton))
					throw new Exception("the last operand of "+op+" can only be of type " + Type.automaton);
				M = operands.get(i).M;
				if(op.equals("E")){
					M.quantify(new HashSet<String>(list_of_identifiers_to_quantify),print,prefix+" ",log);
				} else if (op.equals("A")){
					M.not(print,prefix+" ",log);
					M.quantify(new HashSet<String>(list_of_identifiers_to_quantify),print,prefix+" ",log);
					M.not(print,prefix+" ",log);
				} else {
					M = M.removeLeadingZeroes(list_of_identifiers_to_quantify, print, prefix+" ", log);
					String infReg = M.infinite();
					M = infReg.equals("") ? new Automaton(false) : new Automaton(true);
				}
			}
		}
		stringValue += ")";
		S.push(new Expression(stringValue,M));
		String postStep = prefix + "computed quantifier "+stringValue;  
		log.append(postStep + UtilityMethods.newLine());
		if(print){
			System.out.println(postStep);
		}
	}
}
