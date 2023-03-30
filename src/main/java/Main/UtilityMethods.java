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

import java.util.ArrayList;
import java.util.List;
/**
 * This class contains a number of useful public static method.
 * @author Hamoon
 *
 */
public class UtilityMethods {
	static String dir = "";
	static String ADDRESS_FOR_COMMAND_FILES = "Command Files/";
	static String ADDRESS_FOR_MACRO_LIBRARY = "Macro Library/";
	static String ADDRESS_FOR_AUTOMATA_LIBRARY = "Automata Library/";
	static String ADDRESS_FOR_WORDS_LIBRARY = "Word Automata Library/";
	static String ADDRESS_FOR_MORPHISM_LIBRARY = "Morphism Library/";
	static String ADDRESS_FOR_TRANSDUCER_LIBRARY = "Transducer Library/";
	static String ADDRESS_FOR_RESULT = "Result/";
	static String ADDRESS_FOR_CUSTOM_BASES = "Custom Bases/";
	static String ADDRESS_FOR_TEST_LIBRARY = "Test Library/";
	static String ADDRESS_FOR_INTEGRATION_TEST_RESULTS = "Test Results/Integration Tests/";

	static String PROMPT = "\n[Walnut]$ ";

	public static void setPaths(){
		String path = System.getProperty("user.dir");
		if(path.substring(path.length()-3).equals("bin"))
			dir = "../";
	}

	public static String get_address_for_command_files() {
		return dir + ADDRESS_FOR_COMMAND_FILES;
	}

	public static String get_address_for_automata_library() {
		return dir + ADDRESS_FOR_AUTOMATA_LIBRARY;
	}

	public static String get_address_for_macro_library() {
		return dir + ADDRESS_FOR_MACRO_LIBRARY;
	}

	public static String get_address_for_result() {
		return dir + ADDRESS_FOR_RESULT;
	}

	public static String get_address_for_custom_bases() {
		return dir + ADDRESS_FOR_CUSTOM_BASES;
	}

	public static String get_address_for_words_library() {
		return dir + ADDRESS_FOR_WORDS_LIBRARY;
	}

	public static String get_address_for_morphism_library() {
		return dir + ADDRESS_FOR_MORPHISM_LIBRARY;
	}

	public static String get_address_for_transducer_library() {
		return dir + ADDRESS_FOR_TRANSDUCER_LIBRARY;
	}

	public static String get_address_for_test_library() {
		return dir + ADDRESS_FOR_TEST_LIBRARY;
	}
	public static String get_address_for_integration_test_results() {
		return dir + ADDRESS_FOR_INTEGRATION_TEST_RESULTS;
	}


	public static String newLineString =  System.lineSeparator();
	public static char min(char a,char b){
		if(a < b)return a;
		return b;
	}
	public static char max(char a,char b){
		if(a < b)return b;
		return a;
	}
	public static String newLine(){
		return newLineString;
	}
	/**
	 * checks if a string is \\d+
	 * @param s
	 * @return
	 */
	public static boolean isNumber(String s){
		return s.matches("^\\d+$");
	}

	/**
	 * Checks if a string is neg_\\d+, then return the number but negative.
	 * Otherwise, returns 0.
	 * @param s
	 * @return
	 */
	public static int parseNegNumber(String s){
		if(!s.matches("^neg_\\d+$")) {
			return 0;
		}
		return parseInt(s.substring(4));
	}

	/**
	 * permutes L with regard to permutation. For example if permutation = [1,2,0] then the return value is
	 * [L[1],L[2],L[0]]
	 * @param L
	 * @param permutation
	 * @return
	 */
	public static <T> List<T> permute(List<T> L,int[] permutation){
		List<T> R = new ArrayList<T>(L);
		for(int i = 0 ; i < L.size();i++)
			R.set(permutation[i],L.get(i));
		return R;
	}
	/**
	 * For example when L = [1,2,3] then the result is the string "(1,2,3)"
	 * @param l
	 * @return
	 */
	public static <T> String toTuple(List<T> l){
		String s = "(";
		for(int i = 0; i < l.size();i++){
			if(i == 0)s+=l.get(i);
			else s += ","+l.get(i);
		}

		return s + ")";
	}

	public static <T> String toTransitionLabel(List<T> l) {
		String s = "";
		if (l.size() == 1) {
			s += l.get(0);
			return s;
		}

		s += "[";
		for(int i = 0; i < l.size(); i++){
			if (i == 0) {
				s += l.get(i);
			} else {
				s += "," + l.get(i);
			}
		}

		return s + "]";
	}

	/**
	 * For example when L = [1,3,2,1,3] the result is [1,3,2]
	 * @param L
	 */
	public static <T> void removeDuplicates(List<T> L){
		if(L == null || L.size() <= 1) return;
		List<T> R = new ArrayList<T>();
		for(int i = 0 ; i < L.size();i++){
			boolean flag = true;
			for(int j = 0 ; j < i;j++){
				if(L.get(i).equals(L.get(j))){
					flag = false;
					break;
				}
			}
			if(flag)R.add(L.get(i));
		}
		L.clear();
		L.addAll(R);
	}
	/**
	 * Checks if the set of L and R are equal. L and R does not have duplicates.
	 * @param L
	 * @param R
	 * @return
	 */
	public static <T> boolean areEqual(List<T> L, List<T> R){
		if(L == null && R == null)return true;
		if(L == null || R == null)return false;
		if(L.size() != R.size())return false;
		for(T x:L)
			if(!R.contains(x))return false;
		return true;
	}
	/**
	 * add elements of R that do not exits in L to L.
	 * @param L
	 * @param R
	 */
	public static <T> void addAllWithoutRepetition(List<T> L, List<T> R){
		if(R == null || R.size() == 0)return;
		for(T x:R){
			boolean flag = true;
			for(T y:L){
				if(y.equals(x)){
					flag = false;
					break;
				}
			}
			if(flag)
				L.add(x);
		}
	}
	/**
	 * For example when indices = [1,3] and L = [X,Y,Z,W] then the result is [X,Z]
	 * @param L
	 * @param indices
	 */
	public static <T> void removeIndices(List<T> L, List<Integer> indices) {
		List<T> R = new ArrayList<T>();
		for(int i = 0 ; i < L.size();i++){
			if(indices.indexOf(i) == -1)
				R.add(L.get(i));
		}
		L.clear();
		L.addAll(R);
	}
	/**
	 * @param s
	 * @return
	 */
	public static int parseInt(String s){
		String[] part = s.split("\\s+");
		StringBuffer b = new StringBuffer();
		for(String x:part){
			b.append(x);
		}
		return Integer.parseInt(b.toString());
	}

	/**
	 * Return the common root of two numbers a, b. If no common root exists, return -1.
	 * https://stackoverflow.com/a/72369344/
	 *
	 */
	public static int commonRoot(int a, int b) {
		int temp;

		if (a == 1 || b == 1) {
			return -1;
		}
		else if (a == b) {
			return a;
		}

		// swap if necessary to ensure that a < b
		if (a > b) {
			temp = a;
			a = b;
			b = temp;
		}

		if (b % a == 0) {
			return commonRoot(a, b / a);
		}
		else {
			return -1;
		}
	}

}
