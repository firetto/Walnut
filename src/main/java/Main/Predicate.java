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
import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import Automata.NumberSystem;
import Automata.Automaton;
import Token.AlphabetLetter;
import Token.ArithmeticOperator;
import Token.Function;
import Token.LeftParenthesis;
import Token.LogicalOperator;
import Token.NumberLiteral;
import Token.Operator;
import Token.RelationalOperator;
import Token.RightParenthesis;
import Token.Token;
import Token.Variable;
import Token.Word;

public class Predicate {
	String predicate;
	List<Token> postOrder;
	Stack<Operator> operator_Stack;
	int real_starting_position;
	String default_number_system;
	Matcher MATCHER_FOR_LOGICAL_OPERATORS;
	Matcher MATCHER_FOR_LIST_OF_QUANTIFIED_VARIABLES;
	Matcher MATCHER_FOR_RELATIONAL_OPERATORS;
	Matcher MATCHER_FOR_ARITHMETIC_OPERATORS;
	Matcher MATCHER_FOR_NUMBER_SYSTEM;
	Matcher MATCHER_FOR_WORD;
	Matcher MATCHER_FOR_FUNCTION;
	Matcher MATCHER_FOR_MACRO;
	Matcher MATCHER_FOR_VARIABLE;
	Matcher MATCHER_FOR_NUMBER_LITERAL;
	Matcher MATCHER_FOR_ALPHABET_LETTER;
	Matcher MATCHER_FOR_LEFT_PARENTHESIS;
	Matcher MATCHER_FOR_RIGHT_PARENTHESIS;
	Matcher MATCHER_FOR_WHITESPACE;

	static HashMap<String,NumberSystem> number_system_Hash = new HashMap<String,NumberSystem>();
	public static HashMap<String,NumberSystem> get_number_system_Hash(){
		return number_system_Hash;
	}

	static String REGEXP_FOR_LOGICAL_OPERATORS = "\\G\\s*(`|\\^|\\&|\\~|\\||=>|<=>|E|A|I|\\u02DC|\\u0303)";
	static String REGEXP_FOR_LIST_OF_QUANTIFIED_VARIABLES = "\\G\\s*((\\s*([a-zA-Z&&[^AEI]]\\w*)\\s*)(\\s*,\\s*([a-zA-Z&&[^AEI]]\\w*)\\s*)*)";
	static String REGEXP_FOR_RELATIONAL_OPERATORS = "\\G\\s*(>=|<=|<|>|=|!=)";
	static String REGEXP_FOR_ARITHMETIC_OPERATORS = "\\G\\s*(_|/|\\*|\\+|\\-)";
	static String REGEXP_FOR_NUMBER_SYSTEM = "\\G\\s*\\?(((msd|lsd)_(\\d+|\\w+))|((msd|lsd)(\\d+|\\w+))|(msd|lsd)|(\\d+|\\w+))";
	static String REGEXP_FOR_WORD = "\\G\\s*([a-zA-Z&&[^AEI]]\\w*)\\s*\\[";
	static String REGEXP_FOR_FUNCTION = "\\G\\s*\\$([a-zA-Z&&[^AEI]]\\w*)\\s*\\(";
	static String REGEXP_FOR_MACRO = "\\G(\\s*)\\#([a-zA-Z&&[^AEI]]\\w*)\\s*\\(";
	static String REGEXP_FOR_VARIABLE = "\\G\\s*([a-zA-Z&&[^AEI]]\\w*)";
	static String REGEXP_FOR_NUMBER_LITERAL = "\\G\\s*(\\d+)";
	static String REGEXP_FOR_ALPHABET_LETTER = "\\G\\s*@(\\s*(\\+|\\-)?\\s*\\d+)";
	static String REGEXP_FOR_LEFT_PARENTHESIS = "\\G\\s*\\(";
	static String REGEXP_FOR_RIGHT_PARENTHESIS = "\\G\\s*\\)";
	static String REGEXP_FOR_WHITESPACE = "\\G\\s+";
	static Pattern PATTERN_FOR_LOGICAL_OPERATORS = Pattern.compile(REGEXP_FOR_LOGICAL_OPERATORS);
	static Pattern PATTERN_FOR_LIST_OF_QUANTIFIED_VARIABLES = Pattern.compile(REGEXP_FOR_LIST_OF_QUANTIFIED_VARIABLES);
	static Pattern PATTERN_FOR_RELATIONAL_OPERATORS = Pattern.compile(REGEXP_FOR_RELATIONAL_OPERATORS);
	static Pattern PATTERN_FOR_ARITHMETIC_OPERATORS = Pattern.compile(REGEXP_FOR_ARITHMETIC_OPERATORS);
	static Pattern PATTERN_FOR_NUMBER_SYSTEM = Pattern.compile(REGEXP_FOR_NUMBER_SYSTEM);
	static Pattern PATTERN_FOR_WORD = Pattern.compile(REGEXP_FOR_WORD);
	static Pattern PATTERN_FOR_FUNCTION = Pattern.compile(REGEXP_FOR_FUNCTION);
	static Pattern PATTERN_FOR_MACRO = Pattern.compile(REGEXP_FOR_MACRO);
	static Pattern PATTERN_FOR_VARIABLE = Pattern.compile(REGEXP_FOR_VARIABLE);
	static Pattern PATTERN_FOR_NUMBER_LITERAL = Pattern.compile(REGEXP_FOR_NUMBER_LITERAL);
	static Pattern PATTERN_FOR_ALPHABET_LETTER = Pattern.compile(REGEXP_FOR_ALPHABET_LETTER);
	static Pattern PATTERN_FOR_LEFT_PARENTHESIS = Pattern.compile(REGEXP_FOR_LEFT_PARENTHESIS);
	static Pattern PATTERN_FOR_RIGHT_PARENTHESIS = Pattern.compile(REGEXP_FOR_RIGHT_PARENTHESIS);
	static Pattern PATTERN_FOR_WHITESPACE = Pattern.compile(REGEXP_FOR_WHITESPACE);

	public Predicate(String predicate) throws Exception{
		this("msd_2",predicate,0);
	}
	public Predicate(String predicate,int startingPosition) throws Exception{
		this("msd_2",predicate,startingPosition);
	}
	private void initialize_matchers(){
		MATCHER_FOR_LOGICAL_OPERATORS = PATTERN_FOR_LOGICAL_OPERATORS.matcher(predicate);
		MATCHER_FOR_LIST_OF_QUANTIFIED_VARIABLES = PATTERN_FOR_LIST_OF_QUANTIFIED_VARIABLES.matcher(predicate);
		MATCHER_FOR_RELATIONAL_OPERATORS = PATTERN_FOR_RELATIONAL_OPERATORS.matcher(predicate);
		MATCHER_FOR_ARITHMETIC_OPERATORS = PATTERN_FOR_ARITHMETIC_OPERATORS.matcher(predicate);
		MATCHER_FOR_NUMBER_SYSTEM = PATTERN_FOR_NUMBER_SYSTEM.matcher(predicate);
		MATCHER_FOR_WORD = PATTERN_FOR_WORD.matcher(predicate);
		MATCHER_FOR_FUNCTION = PATTERN_FOR_FUNCTION.matcher(predicate);
		MATCHER_FOR_MACRO = PATTERN_FOR_MACRO.matcher(predicate);
		MATCHER_FOR_VARIABLE = PATTERN_FOR_VARIABLE.matcher(predicate);
		MATCHER_FOR_NUMBER_LITERAL = PATTERN_FOR_NUMBER_LITERAL.matcher(predicate);
		MATCHER_FOR_ALPHABET_LETTER = PATTERN_FOR_ALPHABET_LETTER.matcher(predicate);
		MATCHER_FOR_LEFT_PARENTHESIS = PATTERN_FOR_LEFT_PARENTHESIS.matcher(predicate);
		MATCHER_FOR_RIGHT_PARENTHESIS = PATTERN_FOR_RIGHT_PARENTHESIS.matcher(predicate);
		MATCHER_FOR_WHITESPACE = PATTERN_FOR_WHITESPACE.matcher(predicate);
	}

	public Predicate(
		String default_number_system,
		String predicate,
		int real_starting_position) throws Exception{
		operator_Stack = new Stack<Operator>();
		postOrder = new ArrayList<Token>();
		this.real_starting_position = real_starting_position;
		this.predicate = predicate;
		this.default_number_system = default_number_system;
		if(predicate.matches("^\\s*$"))return;
		initialize_matchers();
		tokenize_and_compute_post_order();
	}

	private void tokenize_and_compute_post_order() throws Exception{
		Stack<String> number_system_Stack = new Stack<String>();
		number_system_Stack.push(default_number_system);
		String current_number_system = default_number_system;
		int index = 0;
		Token t;
		Operator op;
		boolean lastTokenWasOperator = true;
		while(index < predicate.length()){
			if(MATCHER_FOR_LOGICAL_OPERATORS.find(index)) {
				lastTokenWasOperator = true;
				Matcher matcher = MATCHER_FOR_LOGICAL_OPERATORS;
				if(matcher.group(1).equals("E") || matcher.group(1).equals("A") || matcher.group(1).equals("I")){
					if(!MATCHER_FOR_LIST_OF_QUANTIFIED_VARIABLES.find(matcher.end())){
						throw new Exception(
							"Operator " + matcher.group(1) +
							" requires a list of variables: char at " +
							(real_starting_position+index));
					}

					index = handle_quantifier(current_number_system);
				} else {
					op = new LogicalOperator(
						real_starting_position + matcher.start(1), matcher.group(1));
					op.put(postOrder,operator_Stack);
					index = matcher.end();
				}
			} else if(MATCHER_FOR_RELATIONAL_OPERATORS.find(index)) {
				lastTokenWasOperator = true;
				Matcher matcher = MATCHER_FOR_RELATIONAL_OPERATORS;
				if(!number_system_Hash.containsKey(current_number_system)) {
					number_system_Hash.put(current_number_system, new NumberSystem(current_number_system));
				}
				op = new RelationalOperator(real_starting_position + matcher.start(1), matcher.group(1), number_system_Hash.get(current_number_system));
				op.put(postOrder, operator_Stack);
				index = matcher.end();
			} else if(MATCHER_FOR_ARITHMETIC_OPERATORS.find(index)) {
				lastTokenWasOperator = true;
				Matcher matcher = MATCHER_FOR_ARITHMETIC_OPERATORS;
				if(!number_system_Hash.containsKey(current_number_system))
					number_system_Hash.put(current_number_system, new NumberSystem(current_number_system));
				op = new ArithmeticOperator(real_starting_position + matcher.start(1), matcher.group(1), number_system_Hash.get(current_number_system));
				op.put(postOrder,operator_Stack);
				index = matcher.end();
			} else if(MATCHER_FOR_WORD.find(index)) {
				if(!lastTokenWasOperator)throw new Exception(
					"An operator is missing: char at " + (real_starting_position+index));
				lastTokenWasOperator = false;
				index = put_word(current_number_system);
			} else if(MATCHER_FOR_FUNCTION.find(index)) {
				if(!lastTokenWasOperator)throw new Exception(
					"An operator is missing: char at " + (real_starting_position+index));
				lastTokenWasOperator = false;
				index = put_function(current_number_system);
			} else if(MATCHER_FOR_MACRO.find(index)) {
				if(!lastTokenWasOperator)throw new Exception(
					"An operator is missing: char at " + (real_starting_position+index));
				index = put_macro();
			} else if(MATCHER_FOR_VARIABLE.find(index)) {
				if(!lastTokenWasOperator)throw new Exception(
					"An operator is missing: char at " + (real_starting_position+index));
				lastTokenWasOperator = false;
				t = new Variable(real_starting_position + MATCHER_FOR_VARIABLE.start(1),MATCHER_FOR_VARIABLE.group(1));
				t.put(postOrder);
				index = MATCHER_FOR_VARIABLE.end();
			} else if(MATCHER_FOR_NUMBER_LITERAL.find(index)) {
				if(!lastTokenWasOperator)throw new Exception(
					"An operator is missing: char at " + (real_starting_position+index));
				lastTokenWasOperator = false;
				if(!number_system_Hash.containsKey(current_number_system))
					number_system_Hash.put(current_number_system, new NumberSystem(current_number_system));
				t = new NumberLiteral(real_starting_position + MATCHER_FOR_NUMBER_LITERAL.start(1),UtilityMethods.parseInt(MATCHER_FOR_NUMBER_LITERAL.group(1)),number_system_Hash.get(current_number_system));
				t.put(postOrder);
				index = MATCHER_FOR_NUMBER_LITERAL.end();
			} else if(MATCHER_FOR_ALPHABET_LETTER.find(index)) {
				if(!lastTokenWasOperator)throw new Exception("an operator is missing: char at " + index);
				lastTokenWasOperator = false;
				t = new AlphabetLetter(real_starting_position + MATCHER_FOR_ALPHABET_LETTER.start(1),UtilityMethods.parseInt(MATCHER_FOR_ALPHABET_LETTER.group(1)));
				t.put(postOrder);
				index = MATCHER_FOR_ALPHABET_LETTER.end();
			} else if(MATCHER_FOR_NUMBER_SYSTEM.find(index)) {
				String tmp = derive_number_system();
				number_system_Stack.push(tmp);
				current_number_system = tmp;
				index = MATCHER_FOR_NUMBER_SYSTEM.end();
			} else if(MATCHER_FOR_LEFT_PARENTHESIS.find(index)) {
				op = new LeftParenthesis(real_starting_position + index);
				op.put(postOrder,operator_Stack);
				number_system_Stack.push("(");
				index = MATCHER_FOR_LEFT_PARENTHESIS.end();
			} else if(MATCHER_FOR_RIGHT_PARENTHESIS.find(index)) {
				op = new RightParenthesis(real_starting_position + index);
				op.put(postOrder,operator_Stack);
				current_number_system = find_current_number_system_in_stack(number_system_Stack);
				index = MATCHER_FOR_RIGHT_PARENTHESIS.end();
			} else if(MATCHER_FOR_WHITESPACE.find(index)) {
				index = MATCHER_FOR_WHITESPACE.end();
			} else {
				throw new Exception("undefined token: at char "+(real_starting_position + index));
			}
		}

		while(!operator_Stack.isEmpty()){
			op = operator_Stack.pop();
			if(op.isLeftParenthesis()) {
				throw new Exception(
					"Unbalanced parenthesis: char at " + op.getPositionInPredicate());
			} else {
				postOrder.add(op);
			}
		}
	}

	private String find_current_number_system_in_stack(Stack<String> number_system_Stack){
		String current_number_system = default_number_system;
		while(!number_system_Stack.isEmpty()){
			if(number_system_Stack.pop().equals("(")){
				Stack<String> tmp = new Stack<String>();
				while(!number_system_Stack.isEmpty()){
					tmp.push(number_system_Stack.pop());
					if(!tmp.peek().equals("(")){
						current_number_system = tmp.peek();
						break;
					}
				}
				while(!tmp.isEmpty()){
					number_system_Stack.push(tmp.pop());
				}
				break;
			}
		}
		return current_number_system;
	}
	private int handle_quantifier(String numberSystem)throws Exception{
		String[] list_of_vars = MATCHER_FOR_LIST_OF_QUANTIFIED_VARIABLES.group(1).split("(\\s|,)+");
		Operator op = new LogicalOperator(MATCHER_FOR_LOGICAL_OPERATORS.start(), MATCHER_FOR_LOGICAL_OPERATORS.group(1),list_of_vars.length);
		op.put(postOrder, operator_Stack);
		for(String var:list_of_vars){
			Token t = new Variable(MATCHER_FOR_LIST_OF_QUANTIFIED_VARIABLES.start(),var );
			t.put(postOrder);
		}
		return MATCHER_FOR_LIST_OF_QUANTIFIED_VARIABLES.end();
	}
	private String derive_number_system(){
		//"\\G\\s*\\?(((msd|lsd)_(\\d+|\\w+))|((msd|lsd)(\\d+\\w+))|(msd|lsd)|(\\d+|\\w+))";
		if(MATCHER_FOR_NUMBER_SYSTEM.group(2) != null)return MATCHER_FOR_NUMBER_SYSTEM.group(2);
		if(MATCHER_FOR_NUMBER_SYSTEM.group(5) != null)return "msd_"+MATCHER_FOR_NUMBER_SYSTEM.group(5);
		if(MATCHER_FOR_NUMBER_SYSTEM.group(8) != null)return MATCHER_FOR_NUMBER_SYSTEM.group(8)+"_2";
		if(MATCHER_FOR_NUMBER_SYSTEM.group(9) != null)return "msd_"+MATCHER_FOR_NUMBER_SYSTEM.group(9);
		return "msd_2";
	}
	private int put_word(String default_number_system)throws Exception{
		Matcher matcher = MATCHER_FOR_WORD;
		String r_leftBracket = "\\G\\s*\\[";
		Pattern p_leftBracket = Pattern.compile(r_leftBracket);
		Matcher m_leftBracket = p_leftBracket.matcher(predicate);

		Automaton A = new Automaton(UtilityMethods.get_address_for_words_library()+matcher.group(1)+".txt");

		Stack<Character> bracket_Stack = new Stack<Character>();
		bracket_Stack.push('[');
		int i = matcher.end();
		List<Predicate> indices = new ArrayList<Predicate>();
		StringBuffer buf = new StringBuffer();
		int startingPosition = i;
		while(i < predicate.length()){
			char ch = predicate.charAt(i);
			if(ch == ']'){
				if(bracket_Stack.isEmpty())throw new Exception("unbalanced bracket: chat at " + (real_starting_position + i));
				bracket_Stack.pop();
				if(bracket_Stack.isEmpty()){
					indices.add(new Predicate(default_number_system, buf.toString(), real_starting_position + startingPosition));
					buf = new StringBuffer();
					if(m_leftBracket.find(i+1)){
						bracket_Stack.push('[');
						i = m_leftBracket.end();
						startingPosition = i;
						continue;
					}
					else{
						break;
					}
				}
				else
					buf.append(']');
			}
			else{
				buf.append(ch);
				if(ch == '[')bracket_Stack.push('[');
			}
			i++;
		}
		for(Predicate p:indices){
			List<Token> tmp = p.get_postOrder();
			if(tmp.size() == 0)
				throw new Exception("index " + (indices.indexOf(p)+1) + " of the word " + matcher.group(1) + " cannot be empty: char at " + matcher.start(1));
			postOrder.addAll(tmp);
		}
		Word w = new Word(real_starting_position + matcher.start(1), matcher.group(1), A, indices.size());
		w.put(postOrder);
		return i+1;
	}
	private int put_function(String default_number_system)throws Exception{
		Matcher matcher = MATCHER_FOR_FUNCTION;
		Automaton A = new Automaton(UtilityMethods.get_address_for_automata_library()+matcher.group(1)+".txt");
		Stack<Character> parenthesis_Stack = new Stack<Character>();
		parenthesis_Stack.push('(');
		int i = matcher.end();
		List<Predicate> arguments = new ArrayList<Predicate>();
		StringBuffer buf = new StringBuffer();
		int startingPosition = i;
		while(i < predicate.length()){
			char ch = predicate.charAt(i);
			if(ch == '#' || ch == '$'){
				throw new Exception("a function/macro cannot be called from inside another function/macro's argument list: char at " + (real_starting_position+i));
			}
			if(ch == ')'){
				if(parenthesis_Stack.isEmpty())throw new Exception("unbalanced parenthesis: char at " + (real_starting_position + i));
				parenthesis_Stack.pop();
				if(parenthesis_Stack.isEmpty()){
					arguments.add(new Predicate(default_number_system, buf.toString(), real_starting_position + startingPosition));
					break;
				}
				buf.append(')');
			}
			else if(ch == ','){
				if(parenthesis_Stack.size()!=1)throw new Exception("unbalanced parenthesis: char at " + (real_starting_position + i));
				arguments.add(new Predicate(default_number_system, buf.toString(), real_starting_position + startingPosition));
				buf = new StringBuffer();
				startingPosition = i+1;
			}
			else{
				buf.append(ch);
				if(ch == '('){

					parenthesis_Stack.push('(');
				}
			}
			i++;
		}
		if(arguments.size() == 1 && arguments.get(0).get_postOrder().size() == 0){
			arguments.remove(0);
		}
		for(Predicate p:arguments){
			List<Token> tmp = p.get_postOrder();
			if(tmp.size() == 0 && arguments.size() > 1)
				throw new Exception("argument " + (arguments.indexOf(p)+1) + " of the function " + matcher.group(1) + " cannot be empty: char at " + matcher.start(1));
			postOrder.addAll(tmp);
		}
		Function f = new Function(real_starting_position + matcher.start(1), matcher.group(1), A, arguments.size());
		f.put(postOrder);
		return i+1;
	}

	private int put_macro()throws Exception{
		Matcher matcher = MATCHER_FOR_MACRO;

		String macro = "";
		try{
			BufferedReader in =
					new BufferedReader(
							new InputStreamReader(
									new FileInputStream(
											UtilityMethods.get_address_for_macro_library()+matcher.group(2)+".txt"), "utf-8"));
			String line;
			while((line = in.readLine())!= null){
				macro += line;
			}
		}
		catch (IOException e) {
			e.printStackTrace();
			throw new Exception("macro does not exist: " + matcher.group(2));
		}
		Stack<Character> parenthesis_Stack = new Stack<Character>();
		parenthesis_Stack.push('(');
		int i = matcher.end();
		List<String> arguments = new ArrayList<String>();
		StringBuffer buf = new StringBuffer();
		while(i < predicate.length()){
			char ch = predicate.charAt(i);
			if(ch == '#' || ch == '$'){
				throw new Exception("a function/macro cannot be called from inside another function/macro's argument list: char at " + (real_starting_position+i));
			}
			if(ch == ')'){
				if(parenthesis_Stack.isEmpty())throw new Exception("unbalanced parenthesis: char at " + (real_starting_position + i));
				parenthesis_Stack.pop();
				if(parenthesis_Stack.isEmpty()){
					arguments.add(buf.toString());
					break;
				}
				buf.append(')');
			}
			else if(ch == ','){
				if(parenthesis_Stack.size()!=1)throw new Exception("unbalanced parenthesis: char at " + (real_starting_position + i));
				arguments.add(buf.toString());
				buf = new StringBuffer();
			}
			else{
				buf.append(ch);
				if(ch == '('){
					parenthesis_Stack.push('(');
				}
			}
			i++;
		}
		for(int arg_num = arguments.size()-1;arg_num >= 0;arg_num--){
			macro = macro.replaceAll("%"+arg_num, arguments.get(arg_num));
		}
		predicate = predicate.substring(0, matcher.start()) + matcher.group(1) + macro + predicate.substring(i+1);
		initialize_matchers();
		return matcher.start();
	}

	public List<Token> get_postOrder(){
		return postOrder;
	}
	public String toString(){
		String stringValue = "";
		for(int i = 0 ; i < postOrder.size();i++){
			Token t = postOrder.get(i);
			if(i == 0)
				stringValue += t;
			else
				stringValue += ":"+t;
		}
		return stringValue;
	}
}
