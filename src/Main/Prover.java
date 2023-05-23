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
import java.io.BufferedWriter;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.LinkedList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import Automata.Automaton;
import Automata.Morphism;
import Automata.NumberSystem;
import Automata.OstrowskiNumeration;
import Automata.Transducer;

/**
 * This class contains the main method. It is responsible to get a command from user
 * and parse and dispatch the command appropriately.
 * @author Hamoon
 */
public class Prover {
	static String REGEXP_FOR_THE_LIST_OF_COMMANDS = "(eval|def|macro|reg|load|ost|exit|quit|cls|clear|combine|morphism|promote|image|inf|split|rsplit|join|test|transduce|reverse|minimize|convert|fixleadzero|fixtrailzero)";
	static String REGEXP_FOR_EMPTY_COMMAND = "^\\s*(;|::|:)\\s*$";
	/**
	 * the high-level scheme of a command is a name followed by some arguments and ending in either ; : or ::
	 */
	static String REGEXP_FOR_COMMAND = "^\\s*(\\w+)(\\s+.*)?(;|::|:)\\s*$";
	static Pattern PATTERN_FOR_COMMAND = Pattern.compile(REGEXP_FOR_COMMAND);

	static String REGEXP_FOR_exit_COMMAND = "^\\s*(exit|quit)\\s*(;|::|:)$";

	static String REGEXP_FOR_load_COMMAND = "^\\s*load\\s+(\\w+\\.txt)\\s*(;|::|:)\\s*$";
	/**
	 * group for filename in REGEXP_FOR_load_COMMAND
	 */
	static int L_FILENAME = 1;
	static Pattern PATTERN_FOR_load_COMMAND = Pattern.compile(REGEXP_FOR_load_COMMAND);

	static String REGEXP_FOR_eval_def_COMMANDS = "^\\s*(eval|def)\\s+([a-zA-Z]\\w*)((\\s+([a-zA-Z]\\w*))*)\\s+\"(.*)\"\\s*(;|::|:)\\s*$";
	/**
	 * important groups in REGEXP_FOR_eval_def_COMMANDS
	 */
	static int ED_TYPE = 1, ED_NAME = 2, ED_FREE_VARIABLES = 3 ,ED_PREDICATE = 6, ED_ENDING = 7;
	static Pattern PATTERN_FOR_eval_def_COMMANDS = Pattern.compile(REGEXP_FOR_eval_def_COMMANDS);
	static String REXEXP_FOR_A_FREE_VARIABLE_IN_eval_def_COMMANDS = "[a-zA-Z]\\w*";
	static Pattern PATTERN_FOR_A_FREE_VARIABLE_IN_eval_def_COMMANDS = Pattern.compile(REXEXP_FOR_A_FREE_VARIABLE_IN_eval_def_COMMANDS);

	static String REGEXP_FOR_macro_COMMAND = "^\\s*macro\\s+([a-zA-Z]\\w*)\\s+\"(.*)\"\\s*(;|::|:)\\s*$";
	static int M_NAME = 1,M_DEFINITION = 2;
	static Pattern PATTERN_FOR_macro_COMMAND = Pattern.compile(REGEXP_FOR_macro_COMMAND);

	static String REGEXP_FOR_reg_COMMAND = "^\\s*(reg)\\s+([a-zA-Z]\\w*)\\s+((((((msd|lsd)_(\\d+|\\w+))|((msd|lsd)(\\d+|\\w+))|(msd|lsd)|(\\d+|\\w+))|(\\{(\\s*(\\+|\\-)?\\s*\\d+)(\\s*,\\s*(\\+|\\-)?\\s*\\d+)*\\s*\\}))\\s+)+)\"(.*)\"\\s*(;|::|:)\\s*$";

	/**
	 * important groups in REGEXP_FOR_reg_COMMAND
	 */
	static int R_NAME = 2, R_LIST_OF_ALPHABETS = 3, R_REGEXP = 20;
	static Pattern PATTERN_FOR_reg_COMMAND = Pattern.compile(REGEXP_FOR_reg_COMMAND);
	static String REGEXP_FOR_A_SINGLE_ELEMENT_OF_A_SET = "(\\+|\\-)?\\s*\\d+";
	static Pattern PATTERN_FOR_A_SINGLE_ELEMENT_OF_A_SET = Pattern.compile(REGEXP_FOR_A_SINGLE_ELEMENT_OF_A_SET);
	static String REGEXP_FOR_AN_ALPHABET = "((((msd|lsd)_(\\d+|\\w+))|((msd|lsd)(\\d+|\\w+))|(msd|lsd)|(\\d+|\\w+))|(\\{(\\s*(\\+|\\-)?\\s*\\d+)(\\s*,\\s*(\\+|\\-)?\\s*\\d+)*\\s*\\}))\\s+";
	static Pattern PATTERN_FOR_AN_ALPHABET = Pattern.compile(REGEXP_FOR_AN_ALPHABET);
	static int R_NUMBER_SYSTEM = 2,R_SET = 11;

	static String REGEXP_FOR_AN_ALPHABET_VECTOR = "(\\[(\\s*(\\+|\\-)?\\s*\\d+)(\\s*,\\s*(\\+|\\-)?\\s*\\d+)*\\s*\\])|(\\d)";
	static Pattern PATTERN_FOR_AN_ALPHABET_VECTOR = Pattern.compile(REGEXP_FOR_AN_ALPHABET_VECTOR);

	static Pattern PATTERN_FOR_A_SINGLE_NOT_SPACED_WORD = Pattern.compile("\\w+");

	static String REGEXP_FOR_ost_COMMAND = "^\\s*ost\\s+([a-zA-Z]\\w*)\\s*\\[\\s*((\\d+\\s*)*)\\]\\s*\\[\\s*((\\d+\\s*)*)\\]\\s*(;|:|::)\\s*$";
	static Pattern PATTERN_FOR_ost_COMMAND = Pattern.compile(REGEXP_FOR_ost_COMMAND);
	static int GROUP_OST_NAME = 1;
	static int GROUP_OST_PREPERIOD = 2;
	static int GROUP_OST_PERIOD = 4;
	static int GROUP_OST_END = 6;

	static String REGEXP_FOR_combine_COMMAND = "^\\s*combine\\s+([a-zA-Z]\\w*)((\\s+([a-zA-Z]\\w*(=-?\\d+)?))*)\\s*(;|::|:)\\s*$";
	static Pattern PATTERN_FOR_combine_COMMAND = Pattern.compile(REGEXP_FOR_combine_COMMAND);
	static int GROUP_COMBINE_NAME = 1, GROUP_COMBINE_AUTOMATA = 2, GROUP_COMBINE_END = 6;
	static String REGEXP_FOR_AN_AUTOMATON_IN_combine_COMMAND = "([a-zA-Z]\\w*)((=-?\\d+)?)";
	static Pattern PATTERN_FOR_AN_AUTOMATON_IN_combine_COMMAND = Pattern.compile(REGEXP_FOR_AN_AUTOMATON_IN_combine_COMMAND);

	static String REGEXP_FOR_morphism_COMMAND = "^\\s*morphism\\s+([a-zA-Z]\\w*)\\s+\"(\\d+\\s*\\-\\>\\s*(.)*(,\\d+\\s*\\-\\>\\s*(.)*)*)\"\\s*(;|::|:)\\s*$";
	static Pattern PATTERN_FOR_morphism_COMMAND	= Pattern.compile(REGEXP_FOR_morphism_COMMAND);
	static int GROUP_MORPHISM_NAME = 1, GROUP_MORPHISM_DEFINITION;

	static String REGEXP_FOR_promote_COMMAND = "^\\s*promote\\s+([a-zA-Z]\\w*)\\s+([a-zA-Z]\\w*)\\s*(;|::|:)\\s*$";
	static Pattern PATTERN_FOR_promote_COMMAND = Pattern.compile(REGEXP_FOR_promote_COMMAND);
	static int GROUP_PROMOTE_NAME = 1, GROUP_PROMOTE_MORPHISM = 2;

	static String REGEXP_FOR_image_COMMAND = "^\\s*image\\s+([a-zA-Z]\\w*)\\s+([a-zA-Z]\\w*)\\s+([a-zA-Z]\\w*)\\s*(;|::|:)\\s*$";
	static Pattern PATTERN_FOR_image_COMMAND = Pattern.compile(REGEXP_FOR_image_COMMAND);
	static int GROUP_IMAGE_NEW_NAME = 1, GROUP_IMAGE_MORPHISM = 2, GROUP_IMAGE_OLD_NAME = 3;

	static String REGEXP_FOR_inf_COMMAND = "^\\s*inf\\s+([a-zA-Z]\\w*)\\s*(;|::|:)\\s*$";
	static Pattern PATTERN_FOR_inf_COMMAND = Pattern.compile(REGEXP_FOR_inf_COMMAND);
	static int GROUP_INF_NAME = 1;

	static String REGEXP_FOR_split_COMMAND = "^\\s*split\\s+([a-zA-Z]\\w*)\\s+([a-zA-Z]\\w*)((\\s*\\[\\s*[+-]?\\s*])+)\\s*(;|::|:)\\s*$";
	static Pattern PATTERN_FOR_split_COMMAND = Pattern.compile(REGEXP_FOR_split_COMMAND);
	static int GROUP_SPLIT_NAME = 1, GROUP_SPLIT_AUTOMATA = 2, GROUP_SPLIT_INPUT = 3, GROUP_SPLIT_END = 5;
	static String REGEXP_FOR_INPUT_IN_split_COMMAND = "\\[\\s*([+-]?)\\s*]";
	static Pattern PATTERN_FOR_INPUT_IN_split_COMMAND = Pattern.compile(REGEXP_FOR_INPUT_IN_split_COMMAND);

	static String REGEXP_FOR_rsplit_COMMAND = "^\\s*rsplit\\s+([a-zA-Z]\\w*)((\\s*\\[\\s*[+-]?\\s*])+)\\s+([a-zA-Z]\\w*)\\s*(;|::|:)\\s*$";
	static Pattern PATTERN_FOR_rsplit_COMMAND = Pattern.compile(REGEXP_FOR_rsplit_COMMAND);
	static int GROUP_RSPLIT_NAME = 1, GROUP_RSPLIT_AUTOMATA = 4, GROUP_RSPLIT_INPUT = 2, GROUP_RSPLIT_END = 5;
	static String REGEXP_FOR_INPUT_IN_rsplit_COMMAND = "\\[\\s*([+-]?)\\s*]";
	static Pattern PATTERN_FOR_INPUT_IN_rsplit_COMMAND = Pattern.compile(REGEXP_FOR_INPUT_IN_rsplit_COMMAND);

	static String REGEXP_FOR_join_COMMAND = "^\\s*join\\s+([a-zA-Z]\\w*)((\\s+([a-zA-Z]\\w*)((\\s*\\[\\s*[a-zA-Z&&[^AE]]\\w*\\s*])+))*)\\s*(;|::|:)\\s*";
	static Pattern PATTERN_FOR_join_COMMAND = Pattern.compile(REGEXP_FOR_join_COMMAND);
	static int GROUP_JOIN_NAME = 1, GROUP_JOIN_AUTOMATA = 2, GROUP_JOIN_END = 7;
	static String REGEXP_FOR_AN_AUTOMATON_IN_join_COMMAND = "([a-zA-Z]\\w*)((\\s*\\[\\s*[a-zA-Z&&[^AE]]\\w*\\s*])+)";
	static Pattern PATTERN_FOR_AN_AUTOMATON_IN_join_COMMAND = Pattern.compile(REGEXP_FOR_AN_AUTOMATON_IN_join_COMMAND);
	static int GROUP_JOIN_AUTOMATON_NAME = 1, GROUP_JOIN_AUTOMATON_INPUT = 2;
	static String REGEXP_FOR_AN_AUTOMATON_INPUT_IN_join_COMMAND = "\\[\\s*([a-zA-Z&&[^AE]]\\w*)\\s*]";
	static Pattern PATTERN_FOR_AN_AUTOMATON_INPUT_IN_join_COMMAND = Pattern.compile(REGEXP_FOR_AN_AUTOMATON_INPUT_IN_join_COMMAND);

	static String REGEXP_FOR_test_COMMAND = "^\\s*test\\s+([a-zA-Z]\\w*)\\s*(\\d+)\\s*(;|::|:)\\s*$";
	static Pattern PATTERN_FOR_test_COMMAND = Pattern.compile(REGEXP_FOR_test_COMMAND);
	static int GROUP_TEST_NAME = 1, GROUP_TEST_NUM = 2;

	static String REGEXP_FOR_transduce_COMMAND = "^\\s*transduce\\s+([a-zA-Z]\\w*)\\s+([a-zA-Z]\\w*)\\s+(\\$|\\s*)([a-zA-Z]\\w*)\\s*(;|::|:)\\s*$";
	static Pattern PATTERN_FOR_transduce_COMMAND = Pattern.compile(REGEXP_FOR_transduce_COMMAND);
	static int GROUP_TRANSDUCE_NEW_NAME = 1, GROUP_TRANSDUCE_TRANSDUCER = 2,
			GROUP_TRANSDUCE_DOLLAR_SIGN = 3, GROUP_TRANSDUCE_OLD_NAME = 4, GROUP_TRANSDUCE_END = 5;

	static String REGEXP_FOR_reverse_COMMAND = "^\\s*reverse\\s+([a-zA-Z]\\w*)\\s+(\\$|\\s*)([a-zA-Z]\\w*)\\s*(;|::|:)\\s*$";
	static Pattern PATTERN_FOR_reverse_COMMAND = Pattern.compile(REGEXP_FOR_reverse_COMMAND);
	static int GROUP_REVERSE_NEW_NAME = 1, GROUP_REVERSE_DOLLAR_SIGN = 2, GROUP_REVERSE_OLD_NAME = 3, GROUP_REVERSE_END = 4;

	static String REGEXP_FOR_minimize_COMMAND = "^\\s*minimize\\s+([a-zA-Z]\\w*)\\s+([a-zA-Z]\\w*)\\s*(;|::|:)\\s*$";
	static Pattern PATTERN_FOR_minimize_COMMAND = Pattern.compile(REGEXP_FOR_minimize_COMMAND);
	static int GROUP_MINIMIZE_NEW_NAME = 1, GROUP_MINIMIZE_OLD_NAME = 2, GROUP_MINIMIZE_END = 3;

	static String REGEXP_FOR_convert_COMMAND = "^\\s*convert\\s+(\\$|\\s*)([a-zA-Z]\\w*)\\s+((msd|lsd)_(\\d+))\\s+(\\$|\\s*)([a-zA-Z]\\w*)\\s*(;|::|:)\\s*$";
	static Pattern PATTERN_FOR_convert_COMMAND = Pattern.compile(REGEXP_FOR_convert_COMMAND);
	static int GROUP_CONVERT_NEW_NAME = 2, GROUP_CONVERT_OLD_NAME = 7, GROUP_CONVERT_END = 8,
				GROUP_CONVERT_NEW_DOLLAR_SIGN = 1, GROUP_CONVERT_OLD_DOLLAR_SIGN = 6,
				GROUP_CONVERT_NUMBER_SYSTEM = 3, GROUP_CONVERT_MSD_OR_LSD = 4,
				GROUP_CONVERT_BASE = 5;

	static String REGEXP_FOR_fixleadzero_COMMAND = "^\\s*fixleadzero\\s+([a-zA-Z]\\w*)\\s+(\\$|\\s*)([a-zA-Z]\\w*)\\s*(;|::|:)\\s*$";
	static Pattern PATTERN_FOR_fixleadzero_COMMAND = Pattern.compile(REGEXP_FOR_fixleadzero_COMMAND);
	static int GROUP_FIXLEADZERO_NEW_NAME = 1, GROUP_FIXLEADZERO_DOLLAR_SIGN = 2, GROUP_FIXLEADZERO_OLD_NAME = 3, GROUP_FIXLEADZERO_END = 4;

	static String REGEXP_FOR_fixtrailzero_COMMAND = "^\\s*fixtrailzero\\s+([a-zA-Z]\\w*)\\s+(\\$|\\s*)([a-zA-Z]\\w*)\\s*(;|::|:)\\s*$";
	static Pattern PATTERN_FOR_fixtrailzero_COMMAND = Pattern.compile(REGEXP_FOR_fixtrailzero_COMMAND);
	static int GROUP_FIXTRAILZERO_NEW_NAME = 1, GROUP_FIXTRAILZERO_DOLLAR_SIGN = 2, GROUP_FIXTRAILZERO_OLD_NAME = 3, GROUP_FIXTRAILZERO_END = 4;

	/**
	 * if the command line argument is not empty, we treat args[0] as a filename.
	 * if this is the case, we read from the file and load its commands before we submit control to user.
	 * if the the address is not a valid address or the file does not exist, we print an appropriate error message
	 * and submit control to the user.
	 * if the file contains the exit command we terminate the program.
	 * @param args
	 * @throws Exception
	 */
	public static void main(String[] args) throws Exception {
		UtilityMethods.setPaths();

		// to run test cases, run the following lines:
		// IntegrationTest IT = new IntegrationTest(true);
		// IT.runTestCases();



		// WARNING: This will OVERRIDE THE EXISTING TESTS!!!
		// CREATE THE TEST RESULTS MANUALLY INSTEAD, IF YOU CAN!
		// to create test cases, run the following lines:
		// IntegrationTest IT = new IntegrationTest(true);
		// IT.createTestCases();




		// can also run these.
//		IT.runPerformanceTest("Walnut with Valmari without refactoring", 5);
//		IT.runPerformanceTest("Walnut with dk.bricks", 5);

		run(args);
	}

	public static void run(String[] args){
		BufferedReader in = null;
		if(args.length >= 1){
			//reading commands from the file with address args[0]
			try{
				in = new BufferedReader(
					new InputStreamReader(
						new FileInputStream(
							UtilityMethods.get_address_for_command_files() + args[0]),
						"utf-8"));
				if(!readBuffer(in, false)) return;
			}
			catch (IOException e) {
				System.out.flush();
				System.err.println(e.getMessage());
				//e.printStackTrace();
			} finally {
				try {
					if (in != null) {
						in.close();
					}
				} catch (IOException ex) {
					System.out.flush();
					System.err.println(ex.getMessage());
				}
			}
		}

		// Now we parse commands from the console.
		in = new BufferedReader(new InputStreamReader(System.in));
		readBuffer(in, true);
	}

	/**
	 * Takes a BufferedReader and reads from it until we hit end of file or exit command.
	 * @param in
	 * @param console = true if in = System.in
	 * @return
	 */
	public static boolean readBuffer(BufferedReader in, boolean console){
		try{
		    StringBuffer buffer = new StringBuffer();
			while(true) {
				if (console) {
					System.out.print(UtilityMethods.PROMPT);
				}

				String s = in.readLine();
				if(s == null) {
					return true;
				}

		    	int index1 = s.indexOf(';');
		    	int index2 = s.indexOf(':');
		    	int index;
		    	if(index1 != -1 && index2 != -1) {
		    		index = (index1 < index2) ? index1 : index2;
		    	} else if(index1 != -1) {
					index = index1;
				} else {
					index = index2;
				}

		    	if((s.length() - 1) > index && s.charAt(index + 1) == ':') {
		    		index++;
		    	}

		    	if(index != -1) {
		    		s = s.substring(0, index + 1);
		    		buffer.append(s);
		    		s = buffer.toString();
		    		if(!console) {
		    			System.out.println(s);
		    		}

		    		try {
		    			if(!dispatch(s)) {
		    				return false;
		    			}
		    		} catch(Exception e) {
		    			System.out.flush();
		    			System.err.println(e.getMessage() + UtilityMethods.newLine() + "\t: " + s);
		    			System.err.flush();
		    		}

		    		buffer = new StringBuffer();
		    	} else {
		    		buffer.append(s);
		    	}
		    }
		} catch(IOException e) {
			System.out.flush();
			System.err.println(e.getMessage());
			System.err.flush();
		}

		return true;
	}

	public static boolean dispatch(String s) throws Exception{
		if(s.matches(REGEXP_FOR_EMPTY_COMMAND)) {
			// If the command is just ; or : do nothing.
			return true;
		}

		Matcher matcher_for_command = PATTERN_FOR_COMMAND.matcher(s);
		if(!matcher_for_command.find()) {
			throw new Exception("Invalid command.");
		}

		String commandName = matcher_for_command.group(1);
		if(!commandName.matches(REGEXP_FOR_THE_LIST_OF_COMMANDS)) {
			throw new Exception("No such command exists.");
		}

		if(commandName.equals("exit") || commandName.equals("quit")){
			if(s.matches(REGEXP_FOR_exit_COMMAND)) {
				return false;
			}

			throw new Exception("Invalid command.");
		} else if(commandName.equals("load")) {
			if(!loadCommand(s)) return false;
		} else if(commandName.equals("eval") || commandName.equals("def")) {
			eval_def_commands(s);
		} else if(commandName.equals("macro")) {
			macroCommand(s);
		} else if(commandName.equals("reg")) {
			regCommand(s);
		} else if(commandName.equals("ost")) {
			ostCommand(s);
		} else if (commandName.equals("cls") || commandName.equals("clear")) {
			clearScreen();
		} else if (commandName.equals("combine")) {
			combineCommand(s);
		} else if (commandName.equals("morphism")) {
			morphismCommand(s);
		} else if (commandName.equals("promote")) {
			promoteCommand(s);
		} else if (commandName.equals("image")) {
			imageCommand(s);
		} else if (commandName.equals("inf")) {
			infCommand(s);
		} else if (commandName.equals("split")) {
			splitCommand(s);
		} else if (commandName.equals("rsplit")) {
			rsplitCommand(s);
		} else if (commandName.equals("join")) {
			joinCommand(s);
		} else if (commandName.equals("test")) {
			testCommand(s);
		} else if (commandName.equals("transduce")) {
			transduceCommand(s);
		} else if (commandName.equals("reverse")) {
			reverseCommand(s);
		} else if (commandName.equals("minimize")) {
			minimizeCommand(s);
		} else if (commandName.equals("convert")) {
			convertCommand(s);
		} else if (commandName.equals("fixleadzero")) {
			fixLeadZeroCommand(s);
		} else if (commandName.equals("fixtrailzero")) {
			fixTrailZeroCommand(s);
		} else {
			throw new Exception("Invalid command " + commandName + ".");
		}
		return true;
	}

	public static TestCase dispatchForIntegrationTest(String s) throws Exception{
		if(s.matches(REGEXP_FOR_EMPTY_COMMAND)){//if the command is just ; or : do nothing
			return null;
		}

		Matcher matcher_for_command = PATTERN_FOR_COMMAND.matcher(s);
		if(!matcher_for_command.find())throw new Exception("Invalid command.");

		String commandName = matcher_for_command.group(1);
		if(!commandName.matches(REGEXP_FOR_THE_LIST_OF_COMMANDS)) {
			throw new Exception("No such command exists.");
		}

		if(commandName.equals("exit") || commandName.equals("quit")) {
			if(s.matches(REGEXP_FOR_exit_COMMAND)) return null;
			throw new Exception("Invalid command.");
		} else if(commandName.equals("load")){
			if(!loadCommand(s)) return null;
		} else if(commandName.equals("eval") || commandName.equals("def")) {
			return eval_def_commands(s);
		} else if(commandName.equals("macro")) {
			return macroCommand(s);
		} else if(commandName.equals("reg")) {
			return regCommand(s);
		} else if(commandName.equals("combine")) {
			return combineCommand(s);
		} else if(commandName.equals("promote")) {
			return promoteCommand(s);
		} else if(commandName.equals("image")) {
			return imageCommand(s);
		} else if (commandName.equals("split")) {
			return splitCommand(s);
		} else if (commandName.equals("rsplit")) {
			return rsplitCommand(s);
		} else if (commandName.equals("join")) {
			return joinCommand(s);
		} else if (commandName.equals("transduce")) {
			return transduceCommand(s);
		} else if (commandName.equals("reverse")) {
			return reverseCommand(s);
		} else if (commandName.equals("minimize")) {
			return minimizeCommand(s);
		} else if (commandName.equals("convert")) {
			return convertCommand(s);
		} else if (commandName.equals("fixleadzero")) {
			fixLeadZeroCommand(s);
		} else if (commandName.equals("fixtrailzero")) {
			fixTrailZeroCommand(s);
		} else {
			throw new Exception("Invalid command: " + commandName);
		}
		return null;
	}

	/**
	 * load x.p; loads commands from the file x.p. The file can contain any command except for load x.p;
	 * The user don't get a warning if the x.p contains load x.p but the program might end up in an infinite loop.
	 * Note that the file can contain load y.p; whenever y != x and y exist.
	 * @param s
	 * @return
	 * @throws Exception
	 */
	public static boolean loadCommand(String s) throws Exception {
		Matcher m = PATTERN_FOR_load_COMMAND.matcher(s);
		if(!m.find()) throw new Exception("Invalid use of load command.");
		BufferedReader in = null;

		try {
			in = new BufferedReader(
				new InputStreamReader(
					new FileInputStream(
						UtilityMethods.get_address_for_command_files() +
						m.group(L_FILENAME)),
					"utf-8"));
			if(!readBuffer(in,false)) {
				return false;
			}
		} catch (IOException e) {
			System.out.flush();
			System.err.println(e.getMessage());
			System.err.flush();
		}
		return true;
	}

	public static TestCase eval_def_commands(String s) throws Exception {
		Automaton M = null;

		Matcher m = PATTERN_FOR_eval_def_COMMANDS.matcher(s);
		if(!m.find()) {
			throw new Exception("Invalid use of eval/def command.");
		}

		List<String> free_variables = new ArrayList<String>();
		if(m.group(ED_FREE_VARIABLES) != null) {
			which_matrices_to_compute(m.group(ED_FREE_VARIABLES), free_variables);
		}

		boolean printSteps = m.group(ED_ENDING).equals(":");
		boolean printDetails = m.group(ED_ENDING).equals("::");

		Computer c = new Computer(m.group(ED_PREDICATE), printSteps, printDetails);
		c.write(UtilityMethods.get_address_for_result() + m.group(ED_NAME)+".txt");
		c.drawAutomaton(UtilityMethods.get_address_for_result() + m.group(ED_NAME) + ".gv");

		if(free_variables.size() > 0) {
			c.writeMatrices(
				UtilityMethods.get_address_for_result()+m.group(ED_NAME)+".mpl", free_variables);
		}

		c.writeLog(UtilityMethods.get_address_for_result() + m.group(ED_NAME) + "_log.txt");
		if(printDetails) {
			c.writeDetailedLog(
				UtilityMethods.get_address_for_result() + m.group(ED_NAME) + "_detailed_log.txt");
		}

		if(m.group(ED_TYPE).equals("def")) {
			c.write(UtilityMethods.get_address_for_automata_library() + m.group(ED_NAME) + ".txt");
		}

		M = c.getTheFinalResult();
		if (M.TRUE_FALSE_AUTOMATON) {
			if (M.TRUE_AUTOMATON) {
				System.out.println("____\nTRUE");
			} else {
				System.out.println("_____\nFALSE");
			}
		}

		return new TestCase(s, M, "", c.mpl, printDetails ? c.log_details.toString() : "");
	}

	public static TestCase macroCommand(String s) throws Exception {
		Matcher m = PATTERN_FOR_macro_COMMAND.matcher(s);
		if(!m.find())throw new Exception("invalid use of macro command");

		try{
			BufferedWriter out =
					new BufferedWriter(
							new OutputStreamWriter(
									new FileOutputStream(
											UtilityMethods.get_address_for_macro_library()+m.group(M_NAME)+".txt"), "utf-8"));
			out.write(m.group(M_DEFINITION));
			out.close();
		}
		catch (Exception o){
			System.out.println("Could not write the macro " + m.group(M_NAME));
		}
		return null;
	}

	public static TestCase regCommand(String s) throws Exception {
		Matcher m = PATTERN_FOR_reg_COMMAND.matcher(s);
		if(!m.find())throw new Exception("invalid use of reg command");
		NumberSystem ns = null;
		List<List<Integer>> alphabets = new ArrayList<List<Integer>>();
		List<NumberSystem> numSys = new ArrayList<NumberSystem>();
		List<Integer> alphabet = null;
		if(m.group(R_LIST_OF_ALPHABETS) == null) {
			String base = "msd_2";
			try{
				if(!Predicate.number_system_Hash.containsKey(base))
					Predicate.number_system_Hash.put(base, new NumberSystem(base));
				ns = Predicate.number_system_Hash.get(base);
				numSys.add(Predicate.number_system_Hash.get(base));
			}catch(Exception e){
				throw new Exception("number system " + base + " does not exist: char at " + m.start(R_NUMBER_SYSTEM)+UtilityMethods.newLine()+"\t:"+e.getMessage());
			}
			alphabets.add(ns.getAlphabet());
		}
		Matcher m1 = PATTERN_FOR_AN_ALPHABET.matcher(m.group(R_LIST_OF_ALPHABETS));
		while (m1.find()) {
			if((m1.group(R_NUMBER_SYSTEM)!=null)){
				String base = "msd_2";
				if(m1.group(3) != null)base = m1.group(3);
				if(m1.group(6) != null)base = m1.group(7)+"_"+m1.group(8);
				if(m1.group(9) != null)base =  m1.group(9)+"_2";
				if(m1.group(10) != null)base = "msd_"+m1.group(10);
				try{
					if(!Predicate.number_system_Hash.containsKey(base))
						Predicate.number_system_Hash.put(base, new NumberSystem(base));
					ns = Predicate.number_system_Hash.get(base);
					numSys.add(Predicate.number_system_Hash.get(base));
				}catch(Exception e){
					throw new Exception("number system " + base + " does not exist: char at " + m.start(R_NUMBER_SYSTEM)+UtilityMethods.newLine()+"\t:"+e.getMessage());
				}
				alphabets.add(ns.getAlphabet());
			}

			else if(m1.group(R_SET) != null){
				alphabet = what_is_the_alphabet(m1.group(R_SET));
				alphabets.add(alphabet);
				numSys.add(null);
			}
		}
		// To support regular expressions with multiple arity (eg. "[1,0][0,1][0,0]*"), we must translate each of these vectors to an
		// encoding, which will then be turned into a unicode character that dk.brics can work with when constructing an automaton
		// from a regular expression. Since the encoding method is within the Automaton class, we create a dummy instance and load it
		// with our sequence of number systems in order to access it. After the regex automaton is created, we set its alphabet to be the
		// one requested, instead of the unicode alphabet that dk.brics uses.
		Automaton M = new Automaton();
		M.A = alphabets;
		String baseexp = m.group(R_REGEXP);

		Matcher m2 = PATTERN_FOR_AN_ALPHABET_VECTOR.matcher(baseexp);
		// if we haven't had to replace any input vectors with unicode, we use the legacy method of constructing the automaton
		while (m2.find()) {
			List<Integer> L = new ArrayList<Integer>();
			String alphabetVector = m2.group();

			// needed to replace this string with the unicode mapping
			String alphabetVectorCopy = alphabetVector;
			if (alphabetVector.charAt(0) == '[') {
				alphabetVector = alphabetVector.substring(1, alphabetVector.length()-1); // truncate brackets [ ]
			}
			
			Matcher m3 = PATTERN_FOR_A_SINGLE_ELEMENT_OF_A_SET.matcher(alphabetVector);
			while (m3.find()) {
				L.add(UtilityMethods.parseInt(m3.group()));	
			}
			if (L.size() != M.A.size()) {
				throw new Exception("Mismatch between vector length in regex and specified number of inputs to automaton");
			}
			int vectorEncoding = M.encode(L);
			// dk.brics regex has several reserved characters - we cannot use these or the method that generates the automaton will
			// not be able to parse the string properly. All of these reserved characters have UTF-16 values between 0 and 127, so offsetting
			// our encoding by 128 will be enough to ensure that we have no conflicts
			vectorEncoding += 128;
			char replacement = (char)vectorEncoding;
			String replacementStr = Character.toString(replacement);
			
			/**
			 * If alphabetVectorCopy is "2" and baseexp is "(22|[-2][-2])",
			 * and you just run
			 * baseexp.replace(alphabetVectorCopy, replacementStr)
			 * normally, then this will turn baseexp to "(|[-][-])"
			 * instead of "(|[-2][-2])".
			 * Instead, we replace all occurences of "[-2]" with "%PLACEHOLDER%",
			 * then run baseexp.replace(alphabetVectorCopy, replacementStr),
			 * and then replace "%PLACEHOLDER%" with "[-2]". 
			 */
			baseexp = baseexp 
				.replace("[-" + alphabetVectorCopy + "]", "§")
				.replace(alphabetVectorCopy, replacementStr)
				.replace("§", "[-" + alphabetVectorCopy + "]");
		}
		M.alphabetSize = 1;
		for (List<Integer> alphlist : M.A) {
			M.alphabetSize *= alphlist.size();
		}

		// We should always do this with replacement, since we may have regexes such as "...", which accepts any three characters
		// in a row, on an alphabet containing bracketed characters. We don't make any replacements here, but they are implicitly made
		// when we intersect with our alphabet(s).
		Automaton R = new Automaton(baseexp,M.A,M.alphabetSize);
		R.A = M.A;
		R.alphabetSize = M.alphabetSize;
		R.NS = numSys;

		R.draw(UtilityMethods.get_address_for_result()+m.group(R_NAME)+".gv",m.group(R_REGEXP), false);
		R.write(UtilityMethods.get_address_for_result()+m.group(R_NAME)+".txt");
		R.write(UtilityMethods.get_address_for_automata_library()+m.group(R_NAME)+".txt");

		return new TestCase(s,R,"","","");
	}

	public static TestCase combineCommand(String s) throws Exception {
		Matcher m = PATTERN_FOR_combine_COMMAND.matcher(s);
		if(!m.find()) {
			throw new Exception("Invalid use of combine command.");
		}

		boolean printSteps = m.group(GROUP_COMBINE_END).equals(":");
		boolean printDetails = m.group(GROUP_COMBINE_END).equals("::");

		String prefix = new String();
		StringBuffer log = new StringBuffer();


		List<String> automataNames = new ArrayList<String>();
		List<Integer> outputs = new ArrayList<Integer>();
		int argumentCounter = 0;

		Matcher m1 = PATTERN_FOR_AN_AUTOMATON_IN_combine_COMMAND.matcher(m.group(GROUP_COMBINE_AUTOMATA));
		while(m1.find()) {
			argumentCounter++;
			String t = m1.group(1);
			String u = m1.group(2);
			// if no output is specified for a subautomaton, the default output is the index of the subautomaton in the argument list
			if (u.isEmpty()) {
				outputs.add(argumentCounter);
			}
			else {
				u = u.substring(1);
				// remove colon then convert string to integer
				outputs.add(Integer.parseInt(u));
			}
			automataNames.add(t);
		}

		if (automataNames.size() == 0) {
			throw new Exception("Combine requires at least one automaton as input.");
		}
		Automaton first = new Automaton(UtilityMethods.get_address_for_automata_library()+automataNames.get(0)+".txt");
		automataNames.remove(0);

		Automaton C = first.combine(automataNames, outputs, printSteps, prefix, log);
		C.draw(UtilityMethods.get_address_for_result()+m.group(GROUP_COMBINE_NAME)+".gv", s, true);
		C.write(UtilityMethods.get_address_for_result()+m.group(GROUP_COMBINE_NAME)+".txt");
		C.write(UtilityMethods.get_address_for_words_library()+m.group(GROUP_COMBINE_NAME)+".txt");

		return new TestCase(s,C,"","","");
	}

	public static void morphismCommand(String s) throws Exception {
		Matcher m = PATTERN_FOR_morphism_COMMAND.matcher(s);
		if(!m.find()) {
			throw new Exception("Invalid use of morphism command.");
		}
		String name = m.group(GROUP_MORPHISM_NAME);

		Morphism M = new Morphism(name, m.group(GROUP_MORPHISM_DEFINITION));
		System.out.print("Defined with domain ");
        System.out.print(M.mapping.keySet());
        System.out.print(" and range ");
        System.out.print(M.range);
		M.write(UtilityMethods.get_address_for_result()+name+".txt");
		M.write(UtilityMethods.get_address_for_morphism_library()+name+".txt");
	}

	public static TestCase promoteCommand(String s) throws Exception {
		Matcher m = PATTERN_FOR_promote_COMMAND.matcher(s);
		if(!m.find()) {
			throw new Exception("Invalid use of promote command.");
		}
		Morphism h = new Morphism(UtilityMethods.get_address_for_morphism_library()+m.group(GROUP_PROMOTE_MORPHISM)+".txt");
		Automaton P = h.toWordAutomaton();
		P.draw(UtilityMethods.get_address_for_result()+m.group(GROUP_PROMOTE_NAME)+".gv", s, true);
		P.write(UtilityMethods.get_address_for_result()+m.group(GROUP_PROMOTE_NAME)+".txt");
		P.write(UtilityMethods.get_address_for_words_library()+m.group(GROUP_PROMOTE_NAME)+".txt");

		return new TestCase(s,P,"","","");
	}

	public static TestCase imageCommand(String s) throws Exception {
		Matcher m = PATTERN_FOR_image_COMMAND.matcher(s);
		if(!m.find()) {
			throw new Exception("Invalid use of promote command.");
		}
		Morphism h = new Morphism(UtilityMethods.get_address_for_morphism_library()+m.group(GROUP_IMAGE_MORPHISM)+".txt");
		if (!h.isUniform()) {
			throw new Exception("A morphism applied to a word automaton must be uniform.");
		}
		Set<Integer> keys = h.mapping.keySet();
		String combineString = "combine " + m.group(GROUP_IMAGE_NEW_NAME);

		// We need to know the number system of our old automaton: the new one should match, as should intermediary expressions
		Automaton M =  new Automaton(UtilityMethods.get_address_for_words_library()+m.group(GROUP_IMAGE_OLD_NAME)+".txt");
		String numSysName = "";
		if (M.NS.size() > 0) {
			numSysName = M.NS.get(0).toString();
		}

		// we construct a define command for a DFA for each x that accepts iff x appears at the nth position
		for (Integer value : h.range) {
			eval_def_commands(h.makeInterCommand(value, m.group(GROUP_IMAGE_OLD_NAME), numSysName));
			combineString += " " + m.group(GROUP_IMAGE_OLD_NAME) + "_" + value.toString() + "=" + value.toString();
		}
		combineString += ":";

		TestCase retrieval = combineCommand(combineString);
		Automaton I = retrieval.result.clone();
		
		I.draw(UtilityMethods.get_address_for_result()+m.group(GROUP_IMAGE_NEW_NAME)+".gv", s, true);
		I.write(UtilityMethods.get_address_for_result()+m.group(GROUP_IMAGE_NEW_NAME)+".txt");
		I.write(UtilityMethods.get_address_for_words_library()+m.group(GROUP_IMAGE_NEW_NAME)+".txt");
		return new TestCase(s,I,"","","");
	}

	public static boolean infCommand(String s) throws Exception {
		Matcher m = PATTERN_FOR_inf_COMMAND.matcher(s);
		if(!m.find()) {
			throw new Exception("Invalid use of inf command.");
		}
		Automaton M = new Automaton(UtilityMethods.get_address_for_automata_library()+m.group(GROUP_INF_NAME)+".txt");
		M = removeLeadTrailZeroes(M, m.group(GROUP_INF_NAME));
		String infReg = M.infinite();
		if (infReg == "") {
			System.out.println("Automaton " + m.group(GROUP_INF_NAME) + " accepts finitely many values.");
			return false;
		}
		else {
			System.out.println(infReg);
			return true;
		}
	}

	public static TestCase splitCommand(String s) throws Exception {
		Matcher m = PATTERN_FOR_split_COMMAND.matcher(s);
		if(!m.find()) {
			throw new Exception("Invalid use of split command.");
		}
		String addressForWordAutomaton
				= UtilityMethods.get_address_for_words_library()+m.group(GROUP_SPLIT_AUTOMATA)+".txt";
		String addressForAutomaton
				= UtilityMethods.get_address_for_automata_library() + m.group(GROUP_SPLIT_AUTOMATA)+".txt";
		Automaton M; boolean isDFAO;
		if ((new File(addressForWordAutomaton)).exists()) {
			M = new Automaton(addressForWordAutomaton);
			isDFAO = true;
		} else if ((new File(addressForAutomaton)).exists()) {
			M = new Automaton(addressForAutomaton);
			isDFAO = false;
		} else {
			throw new Exception("Automaton " + m.group(GROUP_SPLIT_AUTOMATA) + " does not exist.");
		}

		boolean printSteps = m.group(GROUP_SPLIT_END).equals(":");
		boolean printDetails = m.group(GROUP_SPLIT_END).equals("::");
		String prefix = new String();
		StringBuffer log = new StringBuffer();

		Matcher m1 = PATTERN_FOR_INPUT_IN_split_COMMAND.matcher(m.group(GROUP_SPLIT_INPUT));
		List<String> inputs = new ArrayList<>();
		boolean hasInput = false;
		while(m1.find()) {
			String t = m1.group(1);
			hasInput = hasInput || t.equals("+") || t.equals("-");
			inputs.add(t);
		}
		if(!hasInput || inputs.size() == 0) {
			throw new Exception("Cannot split without inputs.");
		}
		List<Integer> outputs = new ArrayList<>(M.O);
		UtilityMethods.removeDuplicates(outputs);
		List<Automaton> subautomata = M.uncombine(outputs,printSteps,prefix,log);
		for (int i = 0; i < subautomata.size(); i++) {
			Automaton N = subautomata.get(i).split(inputs,printSteps,prefix,log);
			subautomata.set(i, N);
		}
		Automaton N = subautomata.remove(0);
		N = N.combine(new LinkedList<>(subautomata),outputs,printSteps, prefix,log);

		N.draw(UtilityMethods.get_address_for_result()+m.group(GROUP_SPLIT_NAME)+".gv", s, isDFAO);
		N.write(UtilityMethods.get_address_for_result()+m.group(GROUP_SPLIT_NAME)+".txt");
		if (isDFAO) {
			N.write(UtilityMethods.get_address_for_words_library()+m.group(GROUP_SPLIT_NAME)+".txt");
		} else {
			N.write(UtilityMethods.get_address_for_automata_library()+m.group(GROUP_SPLIT_NAME)+".txt");
		}
		return new TestCase(s, N, "", "", "");
	}

	public static TestCase rsplitCommand(String s) throws Exception {
		Matcher m = PATTERN_FOR_rsplit_COMMAND.matcher(s);
		if(!m.find()) {
			throw new Exception("Invalid use of reverse split command.");
		}
		String addressForWordAutomaton
				= UtilityMethods.get_address_for_words_library()+m.group(GROUP_RSPLIT_AUTOMATA)+".txt";
		String addressForAutomaton
				= UtilityMethods.get_address_for_automata_library() + m.group(GROUP_RSPLIT_AUTOMATA)+".txt";
		Automaton M; boolean isDFAO;
		if ((new File(addressForWordAutomaton)).exists()) {
			M = new Automaton(addressForWordAutomaton);
			isDFAO = true;
		} else if ((new File(addressForAutomaton)).exists()) {
			M = new Automaton(addressForAutomaton);
			isDFAO = false;
		} else {
			throw new Exception("Automaton " + m.group(GROUP_RSPLIT_AUTOMATA) + " does not exist.");
		}

		boolean printSteps = m.group(GROUP_RSPLIT_END).equals(":");
		boolean printDetails = m.group(GROUP_RSPLIT_END).equals("::");
		String prefix = new String();
		StringBuffer log = new StringBuffer();

		Matcher m1 = PATTERN_FOR_INPUT_IN_rsplit_COMMAND.matcher(m.group(GROUP_RSPLIT_INPUT));
		List<String> inputs = new ArrayList<>();
		boolean hasInput = false;
		while(m1.find()) {
			String t = m1.group(1);
			hasInput = hasInput || t.equals("+") || t.equals("-");
			inputs.add(t);
		}
		if(!hasInput || inputs.size() == 0) {
			throw new Exception("Cannot split without inputs.");
		}
		List<Integer> outputs = new ArrayList<>(M.O);
		UtilityMethods.removeDuplicates(outputs);
		List<Automaton> subautomata = M.uncombine(outputs,printSteps,prefix,log);
		for (int i = 0; i < subautomata.size(); i++) {
			Automaton N = subautomata.get(i).reverseSplit(inputs,printSteps,prefix,log);
			subautomata.set(i, N);
		}
		Automaton N = subautomata.remove(0);
		N = N.combine(new LinkedList<>(subautomata),outputs,printSteps, prefix,log);

		N.draw(UtilityMethods.get_address_for_result()+m.group(GROUP_RSPLIT_NAME)+".gv", s, isDFAO);
		N.write(UtilityMethods.get_address_for_result()+m.group(GROUP_RSPLIT_NAME)+".txt");
		if (isDFAO) {
			N.write(UtilityMethods.get_address_for_words_library()+m.group(GROUP_RSPLIT_NAME)+".txt");
		} else {
			N.write(UtilityMethods.get_address_for_automata_library()+m.group(GROUP_RSPLIT_NAME)+".txt");
		}
		return new TestCase(s, N, "", "", "");
	}

	public static TestCase joinCommand(String s) throws Exception {
		Matcher m = PATTERN_FOR_join_COMMAND.matcher(s);
		if(!m.find()) {
			throw new Exception("Invalid use of join command.");
		}

		boolean printSteps = m.group(GROUP_JOIN_END).equals(":");
		boolean printDetails = m.group(GROUP_JOIN_END).equals("::");
		String prefix = new String();
		StringBuffer log = new StringBuffer();

		Matcher m1 = PATTERN_FOR_AN_AUTOMATON_IN_join_COMMAND.matcher(m.group(GROUP_JOIN_AUTOMATA));
		List<Automaton> subautomata = new ArrayList<>();
		boolean isDFAO = false;
		while (m1.find()) {
			String automatonName = m1.group(GROUP_JOIN_AUTOMATON_NAME);
			String addressForWordAutomaton
					= UtilityMethods.get_address_for_words_library()+automatonName+".txt";
			String addressForAutomaton
					= UtilityMethods.get_address_for_automata_library()+automatonName+".txt";
			Automaton M;
			if ((new File(addressForWordAutomaton)).exists()) {
				M = new Automaton(addressForWordAutomaton);
				isDFAO = true;
			} else if ((new File(addressForAutomaton)).exists()) {
				M = new Automaton(addressForAutomaton);
			} else {
				throw new Exception("Automaton " + m.group(GROUP_RSPLIT_AUTOMATA) + " does not exist.");
			}

			String automatonInputs = m1.group(GROUP_JOIN_AUTOMATON_INPUT);
			Matcher m2 = PATTERN_FOR_AN_AUTOMATON_INPUT_IN_join_COMMAND.matcher(automatonInputs);
			List<String> label = new ArrayList<>();
			while (m2.find()) {
				String t = m2.group(1);
				label.add(t);
			}
			if (label.size() != M.A.size()) {
				throw new Exception("Number of inputs of word automata " + automatonName + " does not match number of inputs specified.");
			}
			M.label = label;
			subautomata.add(M);
		}
		Automaton N = subautomata.remove(0);
		N = N.join(new LinkedList<>(subautomata),printSteps, prefix,log);

		N.draw(UtilityMethods.get_address_for_result()+m.group(GROUP_JOIN_NAME)+".gv", s, isDFAO);
		N.write(UtilityMethods.get_address_for_result()+m.group(GROUP_JOIN_NAME)+".txt");
		if (isDFAO) {
			N.write(UtilityMethods.get_address_for_words_library()+m.group(GROUP_JOIN_NAME)+".txt");
		} else {
			N.write(UtilityMethods.get_address_for_automata_library()+m.group(GROUP_JOIN_NAME)+".txt");
		}
		return new TestCase(s, N, "", "", "");
	}

	public static void testCommand(String s) throws Exception {
		Matcher m = PATTERN_FOR_test_COMMAND.matcher(s);
		if(!m.find()) {
			throw new Exception("Invalid use of test command.");
		}

		Integer needed = Integer.parseInt(m.group(GROUP_TEST_NUM));

		// We find the first n inputs accepted by our automaton, lexicographically. If less than n inputs are accepted,
    	// we output all that are.
		Automaton M = new Automaton(UtilityMethods.get_address_for_automata_library()+m.group(GROUP_TEST_NAME)+".txt");

		// we don't want to count multiple representations of the same value as distinct accepted values
		M = removeLeadTrailZeroes(M, m.group(GROUP_TEST_NAME));

		// We will be intersecting this automaton with various regex automata, so it needs to be labelled.
		M.randomLabel();

		String infSubcommand = "inf " + m.group(GROUP_TEST_NAME) + ";";
		boolean infinite = infCommand(infSubcommand);
		
		String incLengthReg = "";
		incLengthReg += "reg " + m.group(GROUP_TEST_NAME) + "_len ";
		for (int i=0; i<M.A.size(); i++) {
			String alphaString = M.A.get(i).toString();
			alphaString = alphaString.substring(1, alphaString.length()-1);
			alphaString = "{" + alphaString + "} ";
			incLengthReg += alphaString;
		}

		String dotReg = "";
        int searchLength = 0;
		List<String> accepted = new ArrayList<String>();
        while(true) {
            searchLength++;
            dotReg += ".";
			TestCase retrieval = regCommand(incLengthReg + "\"" + dotReg + "\";");
			Automaton R = retrieval.result.clone();

			// and-ing automata uses the cross product routine, which requires labeled automata
			R.label = M.label;
			Automaton N = M.and(R, false, null, null);
			N.findAccepted(searchLength, needed - accepted.size());
			accepted.addAll(N.accepted);
			if(accepted.size() >= needed) {
				break;
			}

            // If our automaton accepts finitely many inputs, it does not have a non-redundant cycle, and so the highest length input that could be
            // accepted is equal to the number of states in the automaton
            if (!(infinite) && (searchLength >= M.Q)) {
                break;
            }
        }
		if (accepted.size() < needed) {
			System.out.println(m.group(GROUP_TEST_NAME) + " only accepts " + Integer.toString(accepted.size()) + " inputs, which are as follows: ");
		}
		for (String input : accepted) {
			System.out.println(input);
		}
	}

	public static void ostCommand(String s) throws Exception {
		Matcher m = PATTERN_FOR_ost_COMMAND.matcher(s);
		if(!m.find()) {
			throw new Exception("Invalid use of ost command.");
		}

		OstrowskiNumeration ostr = new OstrowskiNumeration(
			m.group(GROUP_OST_NAME),
			m.group(GROUP_OST_PREPERIOD),
			m.group(GROUP_OST_PERIOD));
		ostr.createRepresentationAutomaton();
		ostr.createAdderAutomaton();
	}

	public static TestCase transduceCommand(String s) throws Exception {
		try {
			Matcher m = PATTERN_FOR_transduce_COMMAND.matcher(s);
			if(!m.find()) {
				throw new Exception("Invalid use of transduce command.");
			}

			boolean printSteps = m.group(GROUP_TRANSDUCE_END).equals(":");
			boolean printDetails = m.group(GROUP_TRANSDUCE_END).equals("::");
			String prefix = new String();
			StringBuffer log = new StringBuffer();

			Transducer T = new Transducer(UtilityMethods.get_address_for_transducer_library()+m.group(GROUP_TRANSDUCE_TRANSDUCER)+".txt");
			String library = UtilityMethods.get_address_for_words_library();
			if (m.group(GROUP_TRANSDUCE_DOLLAR_SIGN).equals("$")) {
				library = UtilityMethods.get_address_for_automata_library();
			}
			Automaton M =  new Automaton(library + m.group(GROUP_TRANSDUCE_OLD_NAME)+".txt");

			Automaton C = T.transduceNonDeterministic(M, printSteps || printDetails, prefix, log);
			C.draw(UtilityMethods.get_address_for_result()+m.group(GROUP_TRANSDUCE_NEW_NAME)+".gv", s, true);
			C.write(UtilityMethods.get_address_for_result()+m.group(GROUP_TRANSDUCE_NEW_NAME)+".txt");
			C.write(UtilityMethods.get_address_for_words_library()+m.group(GROUP_TRANSDUCE_NEW_NAME)+".txt");
			return new TestCase(s,C,"","","");
		} catch (Exception e) {
			e.printStackTrace();
			throw new Exception("Error transducing automaton");
		}
	}


	public static TestCase reverseCommand(String s) throws Exception {
		try {
			Matcher m = PATTERN_FOR_reverse_COMMAND.matcher(s);
			if(!m.find()) {
				throw new Exception("Invalid use of reverse command.");
			}

			boolean printSteps = m.group(GROUP_REVERSE_END).equals(":");
			boolean printDetails = m.group(GROUP_REVERSE_END).equals("::");
			String prefix = new String();
			StringBuffer log = new StringBuffer();

			String library = UtilityMethods.get_address_for_words_library();
			if (m.group(GROUP_REVERSE_DOLLAR_SIGN).equals("$")) {
				library = UtilityMethods.get_address_for_automata_library();
			}

			Automaton M = new Automaton(library + m.group(GROUP_REVERSE_OLD_NAME) + ".txt");

			M.reverseWithOutput(true, printSteps || printDetails, prefix, log);
			M.draw(UtilityMethods.get_address_for_result()+m.group(GROUP_REVERSE_NEW_NAME)+".gv", s, true);
			M.write(UtilityMethods.get_address_for_result()+m.group(GROUP_REVERSE_NEW_NAME)+".txt");
			M.write(library + m.group(GROUP_REVERSE_NEW_NAME)+".txt");
			return new TestCase(s,M,"","","");
		} catch (Exception e) {
			e.printStackTrace();
			throw new Exception("Error reversing automaton.");
		}
	}


	public static TestCase minimizeCommand(String s) throws Exception {
		try {
			Matcher m = PATTERN_FOR_minimize_COMMAND.matcher(s);
			if(!m.find()) {
				throw new Exception("Invalid use of minimize command.");
			}

			boolean printSteps = m.group(GROUP_MINIMIZE_END).equals(":");
			boolean printDetails = m.group(GROUP_MINIMIZE_END).equals("::");
			String prefix = new String();
			StringBuffer log = new StringBuffer();

			Automaton M = new Automaton(UtilityMethods.get_address_for_words_library() +
					m.group(GROUP_MINIMIZE_OLD_NAME) + ".txt");

			M.minimizeSelfWithOutput(printSteps || printDetails, prefix, log);

			M.draw(UtilityMethods.get_address_for_result()+m.group(GROUP_MINIMIZE_NEW_NAME)+".gv", s, true);
			M.write(UtilityMethods.get_address_for_result()+m.group(GROUP_MINIMIZE_NEW_NAME)+".txt");
			M.write(UtilityMethods.get_address_for_words_library()+m.group(GROUP_MINIMIZE_NEW_NAME)+".txt");
			return new TestCase(s,M,"","","");
		} catch (Exception e) {
			e.printStackTrace();
			throw new Exception("Error minimizing word automaton.");
		}
	}


	public static TestCase convertCommand(String s) throws Exception {
		try {
			Matcher m = PATTERN_FOR_convert_COMMAND.matcher(s);
			if(!m.find()) {
				throw new Exception("Invalid use of convert command.");
			}

			if (m.group(GROUP_CONVERT_NEW_DOLLAR_SIGN).equals("$")
					&& !m.group(GROUP_CONVERT_OLD_DOLLAR_SIGN).equals("$")) {
				throw new Exception("Cannot convert a Word Automaton into a function");
			}

			String numberSystem = m.group(GROUP_CONVERT_NUMBER_SYSTEM);

			boolean printSteps = m.group(GROUP_CONVERT_END).equals(":");
			boolean printDetails = m.group(GROUP_CONVERT_END).equals("::");
			String prefix = new String();
			StringBuffer log = new StringBuffer();

			String library = UtilityMethods.get_address_for_words_library();
			if (m.group(GROUP_CONVERT_OLD_DOLLAR_SIGN).equals("$")) {
				library = UtilityMethods.get_address_for_automata_library();
			}
			Automaton M =  new Automaton(library + m.group(GROUP_CONVERT_OLD_NAME)+".txt");

			M.convert(m.group(GROUP_CONVERT_MSD_OR_LSD).equals("msd"),
					Integer.parseInt(m.group(GROUP_CONVERT_BASE)), printSteps || printDetails,
					prefix, log);

			M.draw(UtilityMethods.get_address_for_result()+m.group(GROUP_CONVERT_NEW_NAME)+".gv", s, true);
			M.write(UtilityMethods.get_address_for_result()+m.group(GROUP_CONVERT_NEW_NAME)+".txt");

			String outLibrary = UtilityMethods.get_address_for_words_library();
			if (m.group(GROUP_CONVERT_NEW_DOLLAR_SIGN).equals("$")) {
				outLibrary = UtilityMethods.get_address_for_automata_library();
			}
			M.write(outLibrary + m.group(GROUP_CONVERT_NEW_NAME)+".txt");
			return new TestCase(s,M,"","","");
		} catch (Exception e) {
			e.printStackTrace();
			throw new Exception("Error converting automaton.");
		}
	}

	public static TestCase fixLeadZeroCommand(String s) throws Exception {
		try {
			Matcher m = PATTERN_FOR_fixleadzero_COMMAND.matcher(s);
			if(!m.find()) {
				throw new Exception("Invalid use of fixleadzero command.");
			}

			boolean printSteps = m.group(GROUP_FIXLEADZERO_END).equals(":");
			boolean printDetails = m.group(GROUP_FIXLEADZERO_END).equals("::");
			String prefix = new String();
			StringBuffer log = new StringBuffer();

			Automaton M = new Automaton(UtilityMethods.get_address_for_automata_library() + m.group(GROUP_FIXLEADZERO_OLD_NAME) + ".txt");

			M.fixLeadingZerosProblem(printSteps || printDetails, prefix, log);

			M.draw(UtilityMethods.get_address_for_result()+m.group(GROUP_FIXLEADZERO_NEW_NAME)+".gv", s, false);
			M.write(UtilityMethods.get_address_for_result()+m.group(GROUP_FIXLEADZERO_NEW_NAME)+".txt");
			M.write(UtilityMethods.get_address_for_automata_library() + m.group(GROUP_FIXLEADZERO_NEW_NAME)+".txt");
			return new TestCase(s,M,"","","");
		} catch (Exception e) {
			e.printStackTrace();
			throw new Exception("Error fixing leading zeroes for automaton.");
		}
	}

	public static TestCase fixTrailZeroCommand(String s) throws Exception {
		try {
			Matcher m = PATTERN_FOR_fixtrailzero_COMMAND.matcher(s);
			if(!m.find()) {
				throw new Exception("Invalid use of fixtrailzero command.");
			}

			boolean printSteps = m.group(GROUP_FIXTRAILZERO_END).equals(":");
			boolean printDetails = m.group(GROUP_FIXTRAILZERO_END).equals("::");
			String prefix = new String();
			StringBuffer log = new StringBuffer();

			Automaton M = new Automaton(UtilityMethods.get_address_for_automata_library() + m.group(GROUP_FIXTRAILZERO_OLD_NAME) + ".txt");

			M.fixTrailingZerosProblem(printSteps || printDetails, prefix, log);

			M.draw(UtilityMethods.get_address_for_result()+m.group(GROUP_FIXTRAILZERO_NEW_NAME)+".gv", s, false);
			M.write(UtilityMethods.get_address_for_result()+m.group(GROUP_FIXTRAILZERO_NEW_NAME)+".txt");
			M.write(UtilityMethods.get_address_for_automata_library() + m.group(GROUP_FIXTRAILZERO_NEW_NAME)+".txt");
			return new TestCase(s,M,"","","");
		} catch (Exception e) {
			e.printStackTrace();
			throw new Exception("Error fixing trailing zeroes for automaton.");
		}
	}


	public static void clearScreen() {
	    System.out.print("\033[H\033[2J");
	    System.out.flush();
	}

	private static void which_matrices_to_compute(String s, List<String> L){
		Matcher m1 = PATTERN_FOR_A_FREE_VARIABLE_IN_eval_def_COMMANDS.matcher(s);
		while (m1.find()) {
		    String t = m1.group();
		    L.add(t);
		}
	}

	private static List<Integer> what_is_the_alphabet(String s){
		List<Integer> L = new ArrayList<Integer>();
		s = s.substring(1, s.length()-1); //truncation { and } from beginning and end
		Matcher m = PATTERN_FOR_A_SINGLE_ELEMENT_OF_A_SET.matcher(s);
		while(m.find()){
			L.add(UtilityMethods.parseInt(m.group()));
		}
		UtilityMethods.removeDuplicates(L);

		return L;
	}

	private static Automaton removeLeadTrailZeroes(Automaton M, String name) throws Exception {
		// When dealing with enumerating values (eg. inf and test commands), we remove leading zeroes in the case of msd
		// and trailing zeroes in the case of lsd. To do this, we construct a reg subcommand that generates the complement
		// of zero-prefixed strings for msd and zero suffixed strings for lsd, then intersect this with our original automaton.
		M.randomLabel();
		return M.removeLeadingZeroes(M.label, false, null, null);
	}
}
