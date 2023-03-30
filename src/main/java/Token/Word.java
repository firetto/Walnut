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
import java.util.List;
import java.util.Stack;

import Main.Expression;
import Main.UtilityMethods;
import Automata.Automaton;

public class Word extends Token{
	Automaton W;
	String name;
	public Word(int position,String name,Automaton W,int number_of_indices) throws Exception{
		this.name = name;
		setPositionInPredicate(position);
		this.W = W;
		setArity(number_of_indices);
		if(W.getArity() != getArity())throw new Exception("word " + name + " requires " + W.getArity() +" indices: char at " + getPositionInPredicate());
	}
	public String toString(){
		return name;
	}
	public void act(Stack<Expression> S,boolean print,String prefix,StringBuffer log) throws Exception{
		if(S.size() < getArity())throw new Exception("word " + name + " requires " + getArity()+ " indices");
		Stack<Expression> temp = new Stack<Expression>();
		List<Expression> indices = new ArrayList<Expression>();
		for(int i = 1; i <= getArity();i++){
			temp.push(S.pop());
		}
		String stringValue = name;
		String preStep = prefix + "computing " + stringValue+ "[...]";  
		log.append(preStep + UtilityMethods.newLine());
		if(print){
			System.out.println(preStep);
		}
		List<String> identifiers = new ArrayList<String>();
		List<String> quantify = new ArrayList<String>();
		Automaton M = new Automaton(true);
		for(int i = 0 ; i < getArity();i++){
			Expression currentIndex = temp.pop();
			indices.add(currentIndex);
			stringValue += "["+currentIndex+"]";
			/**
			 * type checking
			if(W.NS.get(i) == null && (currentIndex.is(Type.arithmetic) || currentIndex.is(Type.numberLiteral)))
				throw new Exception("index "+ (i+1) +" of word " + name + " cannot be of type arithmetic");	*/
			
			switch(currentIndex.T){
			case variable:				
				if(!identifiers.contains(currentIndex.identifier)){
					identifiers.add(currentIndex.identifier);
				}
				else{
					String new_identifier = currentIndex.identifier+getUniqueString();
					Automaton eq = W.NS.get(i).equality.clone();
					eq.bind(currentIndex.identifier,new_identifier);
					M = M.and(eq,print,prefix+" ",log);
					quantify.add(new_identifier);
					identifiers.add(new_identifier);
				}
				break;
			case arithmetic:
				identifiers.add(currentIndex.identifier);
				M = M.and(currentIndex.M,print,prefix+" ",log);
				quantify.add(currentIndex.identifier);
				break;
			case automaton:
				if(currentIndex.M.getArity() != 1){
					throw new Exception("index " + (i+1) + " of word " + name + " cannot be an automaton with != 1 inputs");
				}
				if(!currentIndex.M.isBound()){
					throw new Exception("index " + (i+1) + " of word " + name + " cannot be an automaton with unlabeled input");					
				}
				M = M.and(currentIndex.M,print,prefix+" ",log);
				identifiers.add(currentIndex.M.getLabel().get(0));
				break;
			case numberLiteral:
				Automaton constant = currentIndex.base.get(currentIndex.constant);
				String id = getUniqueString();
				constant.bind(id);
				identifiers.add(id);
				quantify.add(id);
				M = M.and(constant,print,prefix+" ",log);
				break;
			default:
				throw new Exception("index "+ (i+1) +" of word " + name + " cannot be of type " +currentIndex.getType());			
			}	
		}
		W.bind(identifiers);
		S.push(new Expression(stringValue,W,M,quantify));
		String postStep = prefix + "computed " + stringValue;  
		log.append(postStep + UtilityMethods.newLine());
		if(print){
			System.out.println(postStep);
		}
	}
}
