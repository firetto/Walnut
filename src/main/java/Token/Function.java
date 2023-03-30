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
import Main.UtilityMethods;
import Automata.Automaton;


public class Function extends Token {
	Automaton A;
	String name;
	public Function(int position,String name,Automaton A,int number_of_arguments) throws Exception{
		this.name = name;
		setArity(number_of_arguments);
		setPositionInPredicate(position);
		this.A = A;
		if(A.getArity() != getArity())throw new Exception("function " + name + " requires " + A.getArity() +" arguments: char at " + getPositionInPredicate());
	}
	public String toString(){
		return name;
	}
	public void act(Stack<Expression> S,boolean print,String prefix,StringBuffer log) throws Exception{
		if(S.size() < getArity())throw new Exception("function " + name + " requires " + getArity()+ " arguments");
		Stack<Expression> temp = new Stack<Expression>();
		List<Expression> args = new ArrayList<Expression>();
		for(int i = 0; i < getArity();i++){
			temp.push(S.pop());
		}
		String stringValue = name+"(";
		String preStep = prefix + "computing " + stringValue + "...)";  
		log.append(preStep + UtilityMethods.newLine());
		if(print){
			System.out.println(preStep);
		}
		Automaton M = new Automaton(true);
		List<String> identifiers = new ArrayList<String>();
		List<String> quantify = new ArrayList<String>();
		for(int i = 0 ; i < getArity();i++){
			args.add(temp.pop());
			Expression currentArg = args.get(i);
			if(i == 0)
				stringValue += args.get(i);
			else
				stringValue += ","+args.get(i);
			
			/*if(args.get(i).is(Type.arithmetic) && A.NS.get(i) == null)
				throw new Exception("argument "+ (i+1) +" of function " + name + " cannot be of type arithmetic");
			if(!args.get(i).is(Type.arithmetic) && !args.get(i).is(Type.variable) && !args.get(i).is(Type.numberLiteral))
				throw new Exception("argument "+ (i+1) +" of function " + name + " cannot be of type " +args.get(i).getType());	*/		
			
			switch(currentArg.T){
			case variable:
				if(!identifiers.contains(currentArg.identifier)){
					identifiers.add(currentArg.identifier);
				}
				else{
					String new_identifier = currentArg.identifier+getUniqueString();
					Automaton eq = A.NS.get(i).equality.clone();
					eq.bind(currentArg.identifier,new_identifier);
					M = M.and(eq,print,prefix+" ",log);
					quantify.add(new_identifier);
					identifiers.add(new_identifier);
				}
				break;
			case arithmetic:
				identifiers.add(currentArg.identifier);
				M = M.and(currentArg.M,print,prefix+" ",log);
				quantify.add(currentArg.identifier);
				break;
			case numberLiteral:
				Automaton constant = currentArg.base.get(currentArg.constant);
				String id = getUniqueString();
				constant.bind(id);
				identifiers.add(id);
				quantify.add(id);
				M = M.and(constant,print,prefix+" ",log);
				break;
			case automaton:
				if(currentArg.M.getArity() != 1){
					throw new Exception("argument " + (i+1) + " of function " + name + " cannot be an automaton with != 1 inputs");
				}
				if(!currentArg.M.isBound()){
					throw new Exception("argument " + (i+1) + " of function " + name + " cannot be an automaton with unlabeled input");					
				}
				M = M.and(currentArg.M,print,prefix+" ",log);
				identifiers.add(currentArg.M.getLabel().get(0));
				break;
			default:
				throw new Exception("argument "+ (i+1) +" of function " + name + " cannot be of type " +currentArg.getType());			
			}	
			
		}
		stringValue += ")";
		
		A.bind(identifiers);
		A = A.and(M,print,prefix+" ",log);
		A.quantify(new HashSet<String>(quantify),print,prefix + " ",log);
		
		stringValue += ")";
		S.push(new Expression(stringValue,A));
		String postStep = prefix + "computed " + stringValue;  
		log.append(postStep + UtilityMethods.newLine());
		if(print){
			System.out.println(postStep);
		}
	}
}
