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

package Automata;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.TreeMap;

import Main.UtilityMethods;
/**
 * The class NumberSystem represents a number system.<br>
 * A number system consists of the following four: <br>
 * - a rule to represent non-negative numbers, and hence an alphabet <br>
 * - a rule for addition <br>
 * - a rule for comparison, and by comparison we mean equality and less than testing.<br>
 * - a flag that determines whether numbers are represented in most significant digit order or least significant digit.<br>
 * For example msd_3 is a number system. It is the number system in which <br>
 * - numbers are represented in base 3 in most significant digit first. Hence the alphabet is {0,1,2}.<br>
 * - the rule for addition, is a simple two states automaton, that gets 3-tuples (a,b,c) in base three and
 * accepts iff c=a+b.<br>
 * - the rule for comparison is a simple two state automaton, that gets 2-tuples (a,b) in base three and accepts
 *  iff a < b. <br>
 * - we already mentioned that numbers are in most significant digit first (msd) in this number system. <br>
 *
 * We mandate that 0 and 1 belong to the alphabet of every number systems. In addition, we require that
 * 0* represent the additive identity in all number systems. We also mandate that either
 * 0*1 or 10* (depending on msd/lsd) represent multiplicative
 * identity in all number systems.<br>
 *
 * From here on by rule we mean a finite automaton.
 * If the users want to create a new number system, they, at least, have to provide the rule for addition
 * (in the Custom Bases directory).
 * They can further provide the rule for less than. If less than rule is not provided, we use the lexicographic ordering
 * on integers to create an automaton for less than testing. So for example if the alphabet is {-2,0,7} then in lexicographic order, we have -270 < 0-270-2.<br>
 * Rule for equality is always the rule for word equalities, i.e., two numbers are equal if the words representing
 * them are equal.<br>
 * Rules for base n already exist in the system for every n>1. However the user can override them. <br><br>
 *
 *
 * VERY IMPORTANT: ALL PRIVATE METHODS WHICH RETURN AUTOMATON MUST BE USED WITH CAUTION. THEIR RETURNED AUTOMATON
 * SHOULD NOT BE ALTERED. IF YOU WANT TO ALTER THEIR RETURNED VALUE, THEN YOU HAVE GOT TO MAKE A CLONE AND DO THE
 * MODIFICATION ON THE CLONE.
 */
public class NumberSystem {
	/**
	 * Examples: msd_2, lsd_3, lsd_fib, ...
	 */
	String name;

	/**
	 * is_msd is used to determine which of first or last digit is the most significant digit. It'll be used when we
	 * call Automaton.quantify method, and also in many other places.
	 */
	boolean is_msd;

	/**
	 * is_neg is used to determine whether the base is negative.
	 */
	boolean is_neg;

	/**
	 * Automata for addition, lessThan, and equal<br>
	 * -addition has three inputs, and it accepts
	 *  iff the third is the sum of the first two. So the input is ordered!<br>
	 * -lessThan has two inputs, and it accepts iff the first
	 * one is less than the second one. So the input is ordered!<br>
	 * -equal has two inputs, and it accepts iff they are equal.
	 * -baseChange is defined if the number system has a corresponding comparable negative number system. * Moreover,
	 * baseChange must be initialized manually. comparison_neg accepts inputs x,y if and only if x represents in the
	 * positive base the same non-negative integer as y does in the negative base.
	 */
	public Automaton addition;
	public Automaton lessThan;
	public Automaton equality;
	public Automaton baseChange;
	public Automaton allRepresentations;

	/**
	 * Used to compute constant(n),multiplication(n),division(n) with dynamic programming.
	 * Because these three methods are time consuming, we would like to cache their results in three HashMaps.
	 * For example:<br>
	 * constantsDynamicTable.get(4) is the automaton that has a single input, and accepts if that input equals 4.<br>
	 * multiplicationsDynamicTable(3) is the automaton that gets two inputs, and accepts if the second is 3 times the first. So the input is ordered!<br>
	 * divisionsDynamicTable(5) is the automaton that gets two inputs, and accepts if the second is one-third of the first. So the input is ordered!<br>
	 */
	HashMap<Integer,Automaton> constantsDynamicTable;
	HashMap<Integer,Automaton> multiplicationsDynamicTable;
	HashMap<Integer,Automaton> divisionsDynamicTable;

	boolean flag_should_we_use_allRepresentations = true;

	public boolean isMsd() {
		return is_msd;
	}

	// flips the number system from msd to lsd, and vice versa.
	public void reverseMsd() throws Exception {
		int indexOfUnderscore = name.indexOf("_");
		String msd_or_lsd = name.substring(0, indexOfUnderscore);
		String suffix = name.substring(indexOfUnderscore);
		String newName;
		if (msd_or_lsd.equals("msd")) {
			newName = "lsd" + suffix;
		}
		else {
			newName = "msd" + suffix;
		}
	}

	public String getName() {
		return name;
	}

	public boolean should_we_use_allRepresentations() {
		return flag_should_we_use_allRepresentations;
	}

	public List<Integer> getAlphabet() {
		return addition.A.get(0);
	}

	public Automaton getAllRepresentations() {
		return allRepresentations;
	}

	public NumberSystem(String name) throws Exception{
		this.name = name;
		String msd_or_lsd = name.substring(0, name.indexOf("_"));
		is_msd = msd_or_lsd.equals("msd");
		is_neg = name.contains("neg");
		String base = name.substring(name.indexOf("_") + 1);

		/**
		 * When the number system does not exist, we try to see whether its complement exists or not.
		 * For example lsd_2 is the complement of msd_2.
		 */
		String complementName = (is_msd ? "lsd":"msd")+"_" + base;
		String addressForTheSetOfAllRepresentations =
				UtilityMethods.get_address_for_custom_bases() + name + ".txt";
		String complement_addressForTheSetOfAllRepresentations =
				UtilityMethods.get_address_for_custom_bases() + complementName + ".txt";
		String addressForAddition = UtilityMethods.
				get_address_for_custom_bases() + name + "_addition.txt";
		String complement_addressForAddition = UtilityMethods.
				get_address_for_custom_bases() + complementName + "_addition.txt";
		String addressForLessThan = UtilityMethods.
				get_address_for_custom_bases() + name + "_less_than.txt";
		String complement_addressForLessThan = UtilityMethods.
				get_address_for_custom_bases() + complementName + "_less_than.txt";

		//addition
		if(new File(addressForAddition).isFile()) {
			addition = new Automaton(addressForAddition);
		} else if(new File(complement_addressForAddition).isFile()) {
			addition = new Automaton(complement_addressForAddition);
			addition.reverse(false, null, null, false);
		} else {
			if(UtilityMethods.isNumber(base) && Integer.parseInt(base) > 1) {
				base_n_addition(Integer.parseInt(base));
			} else if(UtilityMethods.parseNegNumber(base) > 1) {
				base_neg_n_addition(UtilityMethods.parseNegNumber(base));
			} else {
				throw new Exception("Number system " + name + " is not defined.");
			}
		}

		/**
		 * The alphabet of all inputs of addition automaton must be equal. It must contain 0 and 1.
		 * The addition automata must have 3 inputs.
		 * All 3 inputs must be of type arithmetic.
		 */
		if(addition.A == null || addition.A.size() != 3) {
			throw new Exception(
					"The addition automaton must have exactly 3 inputs: base " + name);
		}

		if(!addition.A.get(0).contains(0)) {
			throw new Exception(
					"The input alphabet of addition automaton must contain 0: base " + name);
		}

		if(!addition.A.get(0).contains(1)) {
			throw new Exception(
					"The input alphabet of addition automaton must contain 1: base " + name);
		}

		for(int i = 1; i < addition.A.size(); i++) {
			if(!UtilityMethods.areEqual(addition.A.get(i), addition.A.get(0))) {
				throw new Exception(
						"All 3 inputs of the addition automaton " +
								"must have the same alphabet: base " + name);
			}
		}

		for(int i = 0; i < addition.A.size(); i++) {
			addition.NS.set(i, this);
		}

		//lessThan
		if(new File(addressForLessThan).isFile()) {
			lessThan = new Automaton(addressForLessThan);
		} else if(new File(complement_addressForLessThan).isFile()) {
			lessThan = new Automaton(complement_addressForLessThan);
			lessThan.reverse(false,null,null,false);
		} else if(UtilityMethods.parseNegNumber(base) > 1) {
			base_neg_n_less_than(UtilityMethods.parseNegNumber(base));
		} else {
			lexicographicLessThan(addition.A.get(0));
		}

		/**
		 * The lessThan automata must have 2 inputs.
		 * All 2 inputs must be of type arithmetic.
		 * Inputs must have the same alphabet as the addition automaton.
		 */
		if(lessThan.A == null || lessThan.A.size() != 2) {
			throw new Exception(
					"The less_than automaton must have exactly 2 inputs: base " + name);
		}

		for(int i =0; i < lessThan.A.size();i++) {
			if(!UtilityMethods.areEqual(lessThan.A.get(i),addition.A.get(0))) {
				throw new Exception(
						"Inputs of the less_than automaton must have the same alphabet " +
								"as the alphabet of inputs of addition automaton: base " + name);
			}

			lessThan.NS.set(i, this);
		}

		setEquality(addition.A.get(0));

		//the set of all representations
		if(new File(addressForTheSetOfAllRepresentations).isFile()) {
			allRepresentations = new Automaton(addressForTheSetOfAllRepresentations);
		} else if(new File(complement_addressForTheSetOfAllRepresentations).isFile()) {
			allRepresentations = new Automaton(complement_addressForTheSetOfAllRepresentations);
			allRepresentations.reverse(false,null,null, false);
		} else {
			flag_should_we_use_allRepresentations = false;
		}

		if(flag_should_we_use_allRepresentations) {
			for(int i = 0 ; i < allRepresentations.NS.size(); i++) {
				allRepresentations.NS.set(i, this);
			}

			applyAllRepresentations();
		}

		constantsDynamicTable = new HashMap<Integer, Automaton>();
		multiplicationsDynamicTable = new HashMap<>();
		divisionsDynamicTable = new HashMap<>();
	}

	/**
	 * Initializes equality. equality has two inputs, and accepts iff the two inputs are equal.
	 * @param alphabet
	 */
	private void setEquality(List<Integer> alphabet){
		equality = new Automaton();
		equality.Q = 1;
		equality.q0 = 0;
		equality.O.add(1);
		equality.NS.add(this);equality.NS.add(this);
		equality.A.add(new ArrayList<Integer>(alphabet));
        equality.A.add(new ArrayList<Integer>(alphabet));
		equality.alphabetSize = alphabet.size()*alphabet.size();
		equality.d.add(new TreeMap<Integer,List<Integer>>());
		for(int i = 0 ; i < alphabet.size(); i++) {
			List<Integer> dest = new ArrayList<Integer>();
			dest.add(0);
			equality.d.get(0).put(i * alphabet.size() + i, dest);
		}
	}

	/**
	 * Initializes lessThan to lexicographic lessThan. lessThan has two inputs, and it accepts iff the first
	 * one is less than the second one. So the input is ordered!
	 * @param alphabet
	 * @throws Exception
	 */
	private void lexicographicLessThan(List<Integer> alphabet) throws Exception{
		alphabet = new ArrayList<Integer>(alphabet);
		Collections.sort(alphabet);
		lessThan = new Automaton();
		lessThan.Q = 2;
		lessThan.q0 = 0;
		lessThan.O.add(0);lessThan.O.add(1);
		lessThan.NS.add(this);lessThan.NS.add(this);
		lessThan.A.add(new ArrayList<Integer>(alphabet));
        lessThan.A.add(new ArrayList<Integer>(alphabet));
		lessThan.alphabetSize = alphabet.size()*alphabet.size();
		lessThan.d.add(new TreeMap<Integer,List<Integer>>());
        lessThan.d.add(new TreeMap<Integer,List<Integer>>());
		for(int i = 0; i < alphabet.size();i++){
			for(int j = 0 ; j < alphabet.size();j++){
				if(i == j){
					List<Integer> dest = new ArrayList<Integer>();
					dest.add(0);
					lessThan.d.get(0).put(j*alphabet.size()+i,dest);
				}
				if(i < j){
					List<Integer> dest = new ArrayList<Integer>();
					dest.add(1);
					lessThan.d.get(0).put(j*alphabet.size()+i, dest);
				}
				List<Integer> dest = new ArrayList<Integer>();
				dest.add(1);
				lessThan.d.get(1).put(i*alphabet.size()+j, dest);
			}
		}
		if(!is_msd) {
			lessThan.reverse(false,null,null,false);
		}
	}

	/**
	 * Initializes equality of the positive base and negative base if not already set. Equality has two inputs (a,b),
	 * and it accepts iff a in the positive base equals b in the negative base. The current number system can be either
	 * the postive or negative one. This is not initialized for all number systems by default. You should call this
	 * function to initialize as required. If no base_change file is found in the custom bases, we leave the baseChange
	 * automaton unset.
	 * @throws Exception
	 */
	public void setBaseChange() throws Exception {
		if(baseChange != null) return;

		String base = name.substring(name.indexOf("_") + 1);
		String addressForComparison, complement_addressForComparison;
		if(is_neg) {
			addressForComparison = UtilityMethods.
					get_address_for_custom_bases() + name + "_base_change.txt";
			String complementName = (is_msd ? "lsd":"msd")+"_" + base;
			complement_addressForComparison = UtilityMethods.
					get_address_for_custom_bases() + complementName + "_base_change.txt";
		} else {
			String msd_or_lsd = name.substring(0, name.indexOf("_"));
			addressForComparison = UtilityMethods.
					get_address_for_custom_bases() + msd_or_lsd + "_neg_" + base + "_base_change.txt";
			String complementName = (is_msd ? "lsd":"msd")+"_neg_" + base;
			complement_addressForComparison = UtilityMethods.
					get_address_for_custom_bases() + complementName + "_base_change.txt";
		}

		if(new File(addressForComparison).isFile()) {
			baseChange = new Automaton(addressForComparison);
		} else if(new File(complement_addressForComparison).isFile()) {
			baseChange = new Automaton(complement_addressForComparison);
			baseChange.reverse(false, null, null);
		} else if(UtilityMethods.parseNegNumber(base) > 1) {
			base_n_base_change(UtilityMethods.parseNegNumber(base));
		}
		if (baseChange != null) {
			baseChange.applyAllRepresentations();
		}
	}

	private void applyAllRepresentations() throws Exception{
		addition.applyAllRepresentations();
		lessThan.applyAllRepresentations();
		equality.applyAllRepresentations();
	}

	/**
	 * Initializes addition to base n addition. addition has three inputs, and it accepts
	 *  iff the third is the sum of the first two. So the input is ordered!
	 * @param n
	 * @throws Exception
	 */
	private void base_n_addition(int n) throws Exception{
		List<Integer> alphabet = new ArrayList<Integer>();
		for(int i = 0 ; i < n;i++)alphabet.add(i);
		addition = new Automaton();
		addition.Q = 2;
		addition.q0 = 0;
		addition.O.add(1);addition.O.add(0);
		addition.d.add(new TreeMap<Integer,List<Integer>>());
        addition.d.add(new TreeMap<Integer,List<Integer>>());
		addition.NS.add(this);
        addition.NS.add(this);
        addition.NS.add(this);
		addition.A.add(new ArrayList<Integer>(alphabet));
        addition.A.add(new ArrayList<Integer>(alphabet));
        addition.A.add(alphabet);
		addition.alphabetSize = alphabet.size() * alphabet.size() * alphabet.size();
		int l = 0;
		for(int k = 0; k < n;k++){
			for(int j = 0 ; j < n;j++){
				for(int i = 0; i < n;i++){
					if(i+j == k){
						List<Integer> dest = new ArrayList<Integer>();
						dest.add(0);
						addition.d.get(0).put(l,dest);
					}
					if(i+j+1 == k){
						List<Integer> dest = new ArrayList<Integer>();
						dest.add(1);
						addition.d.get(0).put(l, dest);
					}
					if(i+j+1 == k+n){
						List<Integer> dest = new ArrayList<Integer>();
						dest.add(1);
						addition.d.get(1).put(l, dest);
					}
					if(i+j == k+n){
						List<Integer> dest = new ArrayList<Integer>();
						dest.add(0);
						addition.d.get(1).put(l, dest);
					}
					l++;
				}
			}
		}

		if(!is_msd) {
			addition.reverse(false,null,null,false);
        }
	}

	/**
	 * Initializes addition to base negative n addition. addition has three inputs, and it accepts
	 *  iff the third is the sum of the first two. So the input is ordered!
	 * @param n
	 * @throws Exception
	 */
	private void base_neg_n_addition(int n) throws Exception{
		List<Integer> alphabet = new ArrayList<Integer>();
		for(int i = 0 ; i < n;i++)alphabet.add(i);
		addition = new Automaton();
		addition.Q = 3;
		addition.q0 = 0;
		addition.O.add(1);addition.O.add(0);addition.O.add(0);
		addition.d.add(new TreeMap<Integer,List<Integer>>());
		addition.d.add(new TreeMap<Integer,List<Integer>>());
		addition.d.add(new TreeMap<Integer,List<Integer>>());
		addition.NS.add(this);
		addition.NS.add(this);
		addition.NS.add(this);
		addition.A.add(new ArrayList<Integer>(alphabet));
		addition.A.add(new ArrayList<Integer>(alphabet));
		addition.A.add(alphabet);
		addition.alphabetSize = alphabet.size() * alphabet.size() * alphabet.size();
		int l = 0;
		for(int k = 0; k < n;k++){
			for(int j = 0 ; j < n;j++){
				for(int i = 0; i < n;i++){
					if(i+j == k){
						List<Integer> dest = new ArrayList<Integer>();
						dest.add(0);
						addition.d.get(0).put(l,dest);
					}
					if(i+j+1 == k){
						List<Integer> dest = new ArrayList<Integer>();
						dest.add(1);
						addition.d.get(0).put(l, dest);
					}
					if(i+j-1 == k){
						List<Integer> dest = new ArrayList<Integer>();
						dest.add(2);
						addition.d.get(0).put(l, dest);
					}
					if(i+j == k+n){
						List<Integer> dest = new ArrayList<Integer>();
						dest.add(0);
						addition.d.get(2).put(l, dest);
					}
					if(i+j+1 == k+n){
						List<Integer> dest = new ArrayList<Integer>();
						dest.add(1);
						addition.d.get(2).put(l, dest);
					}
					if(i+j-1 == k+n){
						List<Integer> dest = new ArrayList<Integer>();
						dest.add(2);
						addition.d.get(2).put(l, dest);
					}
					if(i == 0 && j == 0 && k == n-1) {
						List<Integer> dest = new ArrayList<Integer>();
						dest.add(2);
						addition.d.get(1).put(l, dest);
					}
					l++;
				}
			}
		}

		if(!is_msd) {
			addition.reverse(false,null,null,false);
		}
	}

	/**
	 * Initializes lessThan to base negative n lessThan. less_than has two inputs, and it accepts
	 *  iff the first is less than the second. So the input is ordered!
	 * @param n
	 * @throws Exception
	 */
	private void base_neg_n_less_than(int n) throws Exception{
		List<Integer> alphabet = new ArrayList<Integer>();
		for(int i = 0 ; i < n;i++)alphabet.add(i);
		lessThan = new Automaton();
		lessThan.Q = 3;
		lessThan.q0 = 0;
		lessThan.O.add(0);lessThan.O.add(1);lessThan.O.add(0);
		lessThan.d.add(new TreeMap<Integer,List<Integer>>());
		lessThan.d.add(new TreeMap<Integer,List<Integer>>());
		lessThan.d.add(new TreeMap<Integer,List<Integer>>());
		lessThan.NS.add(this);
		lessThan.NS.add(this);
		lessThan.A.add(new ArrayList<Integer>(alphabet));
		lessThan.A.add(alphabet);
		lessThan.alphabetSize = alphabet.size() * alphabet.size();
		int l = 0;
		for(int j = 0 ; j < n;j++){
			for(int i = 0; i < n;i++){
				if(i == j){
					List<Integer> dest = new ArrayList<Integer>();
					dest.add(0);
					lessThan.d.get(0).put(l,dest);
				}
				if(i < j){
					List<Integer> dest = new ArrayList<Integer>();
					dest.add(1);
					lessThan.d.get(0).put(l,dest);
				}
				if(j < i){
					List<Integer> dest = new ArrayList<Integer>();
					dest.add(2);
					lessThan.d.get(0).put(l,dest);
				}
				List<Integer> dest_2 = new ArrayList<Integer>();
				dest_2.add(2);
				lessThan.d.get(1).put(l,dest_2);
				List<Integer> dest_1 = new ArrayList<Integer>();
				dest_1.add(1);
				lessThan.d.get(2).put(l,dest_1);
				l++;
			}
		}

		if(!is_msd) {
			lessThan.reverse(false,null,null,false);
		}
	}

	/**
	 * Initializes equality of base n and base -n. Equality has two inputs (a,b), and it accepts
	 * iff [a]_n = [b]_-n (a is a base n representation and b is a base -n representation of
	 * the same integer).
	 * @param n
	 * @throws Exception
	 */
	private void base_n_base_change(int n) throws Exception {
		List<Integer> alphabet = new ArrayList<Integer>();
		for (int i = 0; i < n; i++) alphabet.add(i);
		baseChange = new Automaton();
		baseChange.Q = 4;
		baseChange.q0 = 0;
		baseChange.O.add(1);
		baseChange.O.add(1);
		baseChange.O.add(0);
		baseChange.O.add(0);
		baseChange.d.add(new TreeMap<Integer, List<Integer>>());
		baseChange.d.add(new TreeMap<Integer, List<Integer>>());
		baseChange.d.add(new TreeMap<Integer, List<Integer>>());
		baseChange.d.add(new TreeMap<Integer, List<Integer>>());
		if(is_msd) {
			baseChange.NS.add(new NumberSystem("msd_"+n));
			baseChange.NS.add(new NumberSystem("msd_neg_"+n));
		} else {
			baseChange.NS.add(new NumberSystem("lsd_"+n));
			baseChange.NS.add(new NumberSystem("lsd_neg_"+n));
		}
		baseChange.A.add(new ArrayList<Integer>(alphabet));
		baseChange.A.add(alphabet);
		baseChange.alphabetSize = alphabet.size() * alphabet.size();
		int l = 0;
		for(int j = 0; j < n;j++){
			for(int i = 0 ; i < n;i++){
				if(i == 0 && j == 0){
					List<Integer> dest = new ArrayList<Integer>();
					dest.add(0);
					baseChange.d.get(1).put(l,dest);
				}
				if(i == j){
					List<Integer> dest = new ArrayList<Integer>();
					dest.add(1);
					baseChange.d.get(0).put(l,dest);
				}
				if(i+1 == j){
					List<Integer> dest = new ArrayList<Integer>();
					dest.add(1);
					baseChange.d.get(2).put(l,dest);
				}
				if(i+j == n){
					List<Integer> dest = new ArrayList<Integer>();
					dest.add(2);
					baseChange.d.get(1).put(l,dest);
				}
				if(i+j == n-1){
					List<Integer> dest = new ArrayList<Integer>();
					dest.add(2);
					baseChange.d.get(3).put(l,dest);
				}
				if(i == n-1 && j == 0){
					List<Integer> dest = new ArrayList<Integer>();
					dest.add(3);
					baseChange.d.get(2).put(l,dest);
				}
				l++;
			}
		}

		if(is_msd) {
			baseChange.reverse(false,null,null);
		}
	}

	/**
	 * Gives the corresponding negative number system if one is defined. Throws an exception otherwise.
	 */
	public NumberSystem negative_number_system() throws Exception {
		String msd_or_lsd = name.substring(0, name.indexOf("_"));
		String base = name.substring(name.indexOf("_") + 1);
		return new NumberSystem(msd_or_lsd + "_neg_" + base);
	}

	/**
	 *
	 * @param n
	 * @return an automaton that accepts only n.
	 * If n < 0 and the current number system does not contain negative numbers, then we always return
	 * the false automata. So BE CAREFUL when calling on n < 0.
	 * @throws Exception
	 */
	public Automaton get(int n) throws Exception{
		return constant(n).clone();
	}

	public Automaton getDivision(int n) throws Exception{
		return division(n).clone();
	}

	public Automaton getMultiplication(int n) throws Exception{
		return multiplication(n).clone();
	}

	public String toString(){
		return name;
	}

	/**
	 * @param a
	 * @param b
	 * @param comparisonOperator can be any of "<",">","<=",">=","=","!="
	 * @return an Automaton with two inputs, with labels a and b. It accepts iff a comparisonOperator b.
	 * Note that the order of inputs, in the resulting automaton, is not guaranteed to be either (a,b) or (b,a).
	 * So the input is not ordered!
	 * @throws Exception
	 */
	public Automaton comparison(String a,String b,String comparisonOperator) throws Exception {
		Automaton M;
		switch(comparisonOperator){
			case "<":
				M = lessThan.clone();
				M.bind(a,b);
				break;
			case ">":
				M = lessThan.clone();
				M.bind(b,a);
				break;
			case "=":
				M = equality.clone();
				M.bind(a,b);
				break;
			case "!=":
				M = equality.clone();
				M.bind(a,b);
				M.not(false,null,null);
				break;
			case ">=":
				M = lessThan.clone();
				M.bind(a,b);
				M.not(false,null,null);
				break;
			case "<=":
				M = lessThan.clone();
				M.bind(b,a);
				M.not(false,null,null);
				break;
			default:
				throw new Exception("undefined comparison operator");
		}
		return M;
	}

	/**
	 * @param a
	 * @param b a non negative integer
	 * @param comparisonOperator can be any of "<",">","<=",">=","=","!="
	 * @return an Automaton with single input, with label = [a]. It accepts iff a comparisonOperator b.
	 * @throws Exception
	 */
	public Automaton comparison(String a,int b,String comparisonOperator) throws Exception {
		if(!is_neg && b < 0)throw new Exception("negative constant " + b);
		String B = "new " + a;//this way, we make sure B != a.
		Automaton N,M;
		if (b < 0) {
			M = arithmetic(a,-b,B,"+");
			N = comparison(B, 0,comparisonOperator);
		} else { // b >= 0
			N = get(b);
			if(comparisonOperator.equals("=")){N.bind(a);return N;}
			else if(comparisonOperator.equals("!=")){N.bind(a);N.not(false,null,null);return N;}
			N.bind(B);
			M = comparison(a, B, comparisonOperator);
		}
		M = M.and(N,false,null,null);
		M.quantify(B,false,null,null);
		return M;
	}

	/**
	 * @param a a non negative integer
	 * @param b
	 * @param comparisonOperator can be any of "<",">","<=",">=","=","!="
	 * @return an Automaton with single input, with label = [b]. It accepts iff a comparisonOperator b.
	 * @throws Exception
	 */
	public Automaton comparison(int a,String b,String comparisonOperator) throws Exception {
		if(!is_neg && a < 0)throw new Exception("negative constant " + a);
		switch (comparisonOperator) {
			case "<":
				return comparison(b, a, ">");
			case ">":
				return comparison(b, a, "<");
			case "=":
				return comparison(b, a, "=");
			case "!=":
				return comparison(b, a, "!=");
			case "<=":
				return comparison(b, a, ">=");
			case ">=":
				return comparison(b, a, "<=");
			default:
				throw new Exception("undefined comparison operator");
		}
	}

	/**
	 *
	 * @param a
	 * @param b
	 * @param c
	 * @param arithmeticOperator can be any of "+", "-","*","/"
	 * @return an Automaton with three inputs with labels a,b,c. It accepts iff c = a arithmeticOperator b.
	 * Note that the order of inputs, in the resulting
	 * automaton, is not guaranteed to be in any fixed order like (a,b,c) or (c,b,a) ...
	 * So the input is not ordered!
	 * @throws Exception
	 */
	public Automaton arithmetic(
			String a,
			String b,
			String c,
			String arithmeticOperator) throws Exception {
		Automaton M = addition.clone();
		switch(arithmeticOperator){
			case "+":M.bind(a,b,c);break;
			case "-":M.bind(b,c,a);break;
			case "*":throw new Exception("the operator * cannot be applied to two variables");
			case "/":throw new Exception("the operator / cannot be applied to two variables");
			default:
				throw new Exception("undefined arithmetic operator");
		}
		return M;
	}

	/**
	 *
	 * @param a
	 * @param b an integer
	 * @param c
	 * @param arithmeticOperator can be any of "+","-","*","/"
	 * @return an Automaton with two inputs, with labels a and c. It accepts iff c = a arithmeticOperator b.
	 * Note that the order of inputs, in the resulting
	 * automaton, is not guaranteed to be in any fixed order like [a,c] or [c,a].
	 * So the input is not ordered!
	 * @throws Exception
	 */
	public Automaton arithmetic(
			String a,
			int b,
			String c,
			String arithmeticOperator) throws Exception {
		if(!is_neg && b < 0)throw new Exception("negative constant " + b);
		Automaton N;
		if(arithmeticOperator.equals("*")){
			//note that the case of b = 0 is handled in Computer class
			N = getMultiplication(b);
			N.bind(a,c);
			return N;
		}
		if(arithmeticOperator.equals("/")){
			if(b == 0)throw new Exception("division by zero");
			N = getDivision(b);
			N.bind(a,c);
			return N;
		}

		Automaton M;
		String B = a+c; //this way we make sure that B is not equal to a or c
		if(b < 0) { // We rewrite "a-b=c" as "a+(-b)=c" and "a+b=c" as "a-(-b)=c"
			N = get(-b);
			N.bind(B);
			M = arithmetic(a, B, c, arithmeticOperator.equals("+") ? "-" : "+");
		} else { // b >= 0
			N = get(b);
			N.bind(B);
			M = arithmetic(a, B, c, arithmeticOperator);
		}
		M = M.and(N,false,null,null);
		M.quantify(B,false,null,null);
		return M;
	}

	/**
	 *
	 * @param a an integer
	 * @param b
	 * @param c
	 * @param arithmeticOperator can be any of "+","-","*","/"
	 * @return an Automaton with two inputs, with labels b and c. It accepts iff c = a arithmeticOperator b.
	 * Note that the order of inputs, in the resulting
	 * automaton, is not guaranteed to be in any fixed order like [b,c] or [c,b].
	 * So the input is not ordered!
	 * @throws Exception
	 *
	 */
	public Automaton arithmetic(
		int a,
		String b,
		String c,
		String arithmeticOperator) throws Exception {
		if(!is_neg && a < 0)throw new Exception("negative constant " + a);
		Automaton N;
		if(arithmeticOperator.equals("*")){
			N = getMultiplication(a);
			N.bind(b,c);
			return N;
		}
		if(arithmeticOperator.equals("/"))
			throw new Exception("constants cannot be divided by variables");

		Automaton M;
		String A = b+c; //this way we make sure that A is not equal to b or c
		if(a < 0 && arithmeticOperator.equals("+")) { // We rewrite "a+b=c" and "c+(-a)=b"
			N = get(-a);
			N.bind(A);
			M = arithmetic(c, A, b, arithmeticOperator);
		} else if(a < 0 && arithmeticOperator.equals("-")) { // Notice "a-b=c" is false unless we are in a negative base
			// So we may call get(a) where a < 0
			N = get(a);
			N.bind(A);
			M = arithmetic(A, b, c, arithmeticOperator);
		} else { // a >= 0
			N = get(a);
			N.bind(A);
			M = arithmetic(A, b, c, arithmeticOperator);
		}
		M = M.and(N,false,null,null);
		M.quantify(A,false,null,null);
		return M;
	}

	/**
	 *
	 * @param a
	 * @param b
	 * @param c an integer
	 * @param arithmeticOperator can be any of "+","-","*","/"
	 * @return an Automaton with two inputs, with labels b and c. It accepts iff c = a arithmeticOperator b.
	 * Note that the order of inputs, in the resulting
	 * automaton, is not guaranteed to be in any fixed order like [a,b] or [b,a].
	 * So the input is not ordered!
	 * @throws Exception
	 *
	 */
	public Automaton arithmetic(
			String a,
			String b,
			int c,
			String arithmeticOperator) throws Exception {
		if(!is_neg && c < 0)throw new Exception("negative constant " + c);
		Automaton N;
		if(arithmeticOperator.equals("*")) {
			throw new Exception("the operator * cannot be applied to two variables");
		} else if(arithmeticOperator.equals("/"))
			throw new Exception("the operator / cannot be applied to two variables");

		Automaton M;
		String C = a+b; //this way we make sure that A is not equal to a or b
		if(c < 0 && arithmeticOperator.equals("-")) { // We rewrite "a-b=c" and "a+(-c)=b"
			N = get(-c);
			N.bind(C);
			M = arithmetic(a, C, b, arithmeticOperator);
		} else if (c < 0 && arithmeticOperator.equals("+")) { // Notice "a+b=c" is false unless we are in a negative base
			// So we may call get(c) where c < 0
			N = get(c);
			N.bind(C);
			M = arithmetic(a, b, C, arithmeticOperator);
		} else { // c >= 0
			N = get(c);
			N.bind(C);
			M = arithmetic(a, b, C, arithmeticOperator);
		}
		M = M.and(N,false,null,null);
		M.quantify(C,false,null,null);
		return M;
	}

	/**
	 *
	 * @param n
	 * @return an Automaton with one input. It accepts when the input equals n.
	 * @throws Exception
	 */
	private Automaton constant(int n) throws Exception {
		if (!is_neg && n < 0) {
			throw new Exception("Constant cannot be negative.");
		}
		if (constantsDynamicTable.containsKey(n)) {
			return constantsDynamicTable.get(n);
		}

		Automaton P;
		if (n == 0) {
			P = make_zero();
		} else if (n == 1) {
			P = make_one();
		} else if (n < 0) {
			String a = "a",b = "b";
			// b = -n
			Automaton M = get(-n);
			M.bind(b);
			// Eb, a + b = 0 & b = -n
			P = arithmetic(a,b,0, "+");
			P = P.and(M, false, null, null);
			P.quantify(b, false, null, null);
		} else { // n > 0
			String a = "a", b = "b", c = "c";
			// a = floor(n/2)
			Automaton M = get(n/2);
			M.bind(a);
			// b = ciel(n/2)
			Automaton N = get(n/2 + (n%2 == 0 ? 0:1));
			N.bind(b);
			// Ea,Eb, a + b = c & a = floor(n/2) & b = ciel(n/2)
			P = arithmetic(a,b,c, "+");
			P = P.and(M, false, null, null);
			P = P.and(N, false, null, null);
			P.quantify(a, b, is_msd, false, null, null);
		}
		constantsDynamicTable.put(n, P);
		return P;
	}

	/**
	 * The returned automaton has two inputs, and it accepts iff the second is n times the first. So the input is ordered!
	 * @param n
	 * @return
	 * @throws Exception
	 */
	private Automaton multiplication(int n)throws Exception {
		if(!is_neg && n < 0)throw new Exception("constant cannot be negative");
		if(n == 0)throw new Exception("multiplication(0)");
		if(multiplicationsDynamicTable.containsKey(n))return multiplicationsDynamicTable.get(n);
		//note that the case of n==0 is handled in Computer class
		Automaton P;
		if(n == 1){
			P = equality;
		} else if (n < 0) {
			String a = "a",b = "b",c = "c";
			// c = (-n)*a
			Automaton M = getMultiplication(-n);
			M.bind(a,c);
			// Ec b + c = 0 & c = (-n)*a
			P = arithmetic(b,c,0, "+");
			P = P.and(M, false, null, null);
			P.quantify(c,false,null,null);
			P.sortLabel();
		} else { // n > 1
			String a = "a",b = "b",c = "c",d = "d";
			//b = floor(n/2)*a
			Automaton M = getMultiplication(n/2);
			M.bind(a,b);
			//c = ceil(n/2)*a
			Automaton N = getMultiplication(n/2 + (n%2 == 0 ? 0:1));
			N.bind(a,c);
			// Eb,Ec, b + c = d & b = floor(n/2)*a & c = ciel(n/2)*a
			P = arithmetic(b, c, d, "+");
			P = P.and(M,false,null,null);
			P = P.and(N,false,null,null);
			P.quantify(b,c,is_msd,false,null,null);
			P.sortLabel();
		}
		multiplicationsDynamicTable.put(n, P);
		return P;
	}

	/**
	 * The returned automaton has two inputs, and it accepts iff the second is one nth of the first. So the input is ordered!
	 * @param n
	 * @return
	 * @throws Exception
	 */
	// a / n = b <=> Er,q a = q + r & q = n*b & n < r <= 0 if n < 0
	private Automaton division(int n)throws Exception {
		if(!is_neg && n < 0)throw new Exception("constant cannot be negative");
		if(n == 0)throw new Exception("division by zero");
		if(divisionsDynamicTable.containsKey(n))return divisionsDynamicTable.get(n);
		String a = "a",b = "b",r = "r",q = "q";
		// We want to construct the following expressions
		// a / n = b <=> Er,q a = q + r & q = n*b & n < r <= 0 if n < 0
		// a / n = b <=> Er,q a = q + r & q = n*b & 0 <= r < n if n > 0
		Automaton M = arithmetic(q,r,a,"+");
		Automaton N = arithmetic(n,b,q,"*");
		Automaton P1, P2;
		if (n < 0) {
			// n < 0 <= 0
			P1 = comparison(r,0, "<=");
			P2 = comparison(r,n, ">");
		} else { // n > 0
			// 0 <= r < n
			P1 = comparison(r,0, ">=");
			P2 = comparison(r,n, "<");
		}
		Automaton P = P1.and(P2,false,null,null);
		Automaton R = M.and(N,false,null,null);
		R = R.and(P,false,null,null);
		R.quantify(q,r, is_msd,false,null,null);
		R.sortLabel();
		divisionsDynamicTable.put(n, R);
		return R;
	}

	private Automaton make_zero()throws Exception {
		List<Integer> alph = new ArrayList<Integer>();
		alph.add(0);
		alph.add(1);
		Automaton M = new Automaton("0*",alph,this);
		M.A = new ArrayList<List<Integer>>();
		M.A.add(new ArrayList<Integer>(addition.A.get(0)));
		M.alphabetSize = M.A.get(0).size();
		M.encoder = new ArrayList<Integer>();
		M.encoder.add(1);
		M.canonize();
		constantsDynamicTable.put(0, M);
		return M;
	}

	private Automaton make_one() throws Exception {
		List<Integer> alph = new ArrayList<Integer>();
		alph.add(0);
		alph.add(1);
		Automaton M = new Automaton("0*",alph,this);
		if(is_msd)
			M = new Automaton("0*1",alph,this);
		else
			M = new Automaton("10*",alph,this);
		M.A = new ArrayList<List<Integer>>();
		M.A.add(new ArrayList<Integer>(addition.A.get(0)));
		M.alphabetSize = M.A.get(0).size();
		M.encoder = new ArrayList<Integer>();
		M.encoder.add(1);
		M.canonize();
		constantsDynamicTable.put(1, M);
		return M;
	}
}
