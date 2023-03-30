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
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import Automata.Automaton;

public class IntegrationTest {
	String directoryAddress = UtilityMethods.get_address_for_integration_test_results();
	String performanceTestFileName = "performance_test.txt";
	List<TestCase> testCases;//list of test cases
	List<String> L;//list of commands
	private void initialize(){
		PrintWriter out = null;
		try {
			File file = new File(UtilityMethods.get_address_for_words_library() + "T2.txt");
			file.getParentFile().mkdirs();
			out = new PrintWriter(UtilityMethods.get_address_for_words_library() + "T2.txt", "utf-8");
			out.write("msd_2 msd_2\n0 1\n0 0 -> 0\n1 0 -> 1\n0 1 -> 1\n1 1 -> 0\n1 0\n0 0 -> 1\n1 0 -> 0\n0 1 -> 0\n1 1 -> 1\n");
			out.close();
			out = new PrintWriter(UtilityMethods.get_address_for_words_library() + "RS.txt", "utf-8");
			out.write("msd_2\n0 0\n0 -> 0\n1 -> 1\n1 0\n0 -> 0\n1 -> 2\n2 1\n0 -> 3\n1 -> 1\n3 1\n0 -> 3\n1 -> 2\n");
			out.close();
			out = new PrintWriter(UtilityMethods.get_address_for_words_library() + "P.txt", "utf-8");
			out.write("msd_2\n0 0\n0 -> 0\n1 -> 1\n1 0\n0 -> 0\n1 -> 2\n2 1\n0 -> 3\n1 -> 2\n3 1\n0 -> 3\n1 -> 1\n");
			out.close();
			out = new PrintWriter(UtilityMethods.get_address_for_words_library() + "PR.txt", "utf-8");
			out.write("lsd_2\n0 0\n0 -> 1\n1 -> 0\n1 0\n0 -> 2\n1 -> 3\n2 0\n0 -> 2\n1 -> 2\n3 1\n0 -> 3\n1 -> 3\n");
			out.close();
			out = new PrintWriter(UtilityMethods.get_address_for_words_library() + "PD.txt", "utf-8");
			out.write("msd_2\n0 1\n0 -> 0\n1 -> 1\n1 0\n0 -> 0\n1 -> 0\n");
			out.close();

			Prover.dispatch("reg endsIn2Zeros lsd_2 \"(0|1)*00\";");
			Prover.dispatch("reg startsWith2Zeros msd_2 \"00(0|1)*\";");
			Prover.dispatchForIntegrationTest("def thueeq \"T[x]=T[y]\";");
			Prover.dispatchForIntegrationTest("def func \"(?msd_3 c < 5) & (a = b+1) & (?msd_10 e = 17)\";");
			Prover.dispatchForIntegrationTest("def thuefactoreq \"Ak (k < n) => T[i+k] = T[j+k]\";");
			Prover.dispatchForIntegrationTest("def thueuniquepref \"Aj (j > 0 & j < n-m) => ~$thuefactoreq(i,i+j,m)\";");
			Prover.dispatchForIntegrationTest("def thueuniquesuff \"Aj (j > 0 & j < n-m) => ~$thuefactoreq(i+n-m,i+n-m-j,m)\";");
			Prover.dispatchForIntegrationTest("def thuepriv \"(n >= 1) & Am (m <= n & m >= 1) => (Ep (p <= m & p >= 1) & $thueuniquepref(i,p,m) & $thueuniquesuff(i+n-m,p,m) & $thuefactoreq(i, i+n-p, p))\";");
			Prover.dispatchForIntegrationTest("def fibmr \"?msd_fib (i<=j)&(j<n)&Ep ((p>=1)&(2*p+i<=j+1)&(Ak (k+i+p<=j) => (F[i+k]=F[i+k+p]))&((i>=1) => (Aq ((1<=q)&(q<=p)) =>"
											+ "(El (l+i+q<=j+1)&(F[i+l-1]!=F[i+l+q-1]))))&((j+2<=n) => (Ar ((1<=r)&(r<=p)) =>"
											+ "(Em (m+r+i<=j+1)&(F[i+m]!=F[i+m+r])))))\";");

			Prover.dispatchForIntegrationTest("load thue_tests.txt;");
			Prover.dispatchForIntegrationTest("load rudin_shapiro_tests.txt;");
			Prover.dispatchForIntegrationTest("load rudin_shapiro_trapezoidal_tests.txt;");
			Prover.dispatchForIntegrationTest("load paperfolding_tests.txt;");
			Prover.dispatchForIntegrationTest("load paperfolding_trapezoidal_tests.txt;");
			Prover.dispatchForIntegrationTest("load period_doubling_tests.txt;");
			Prover.dispatchForIntegrationTest("load fibonacci_tests.txt;");
			Prover.dispatchForIntegrationTest("load morphism_image_tests.txt;");

			Prover.dispatchForIntegrationTest("macro palindrome \"?%0 Ak (k<n) => %1[i+k] = %1[i+n-1-k]\";");
			//Prover.dispatchForIntegrationTest("macro factoreq \"%0 Ak (%4<n) => %1[%2+k]=%1[%3+k]\"");
			Prover.dispatchForIntegrationTest("macro border \"?%0 m>=1 & m<=n & $%1_factoreq(i,i+n-m,m)\";");
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (UnsupportedEncodingException e) {
			e.printStackTrace();
		} catch(Exception e){
			e.printStackTrace();
		} finally {
	        if(out != null){
	            out.close();
	        }
        }
	}
	public IntegrationTest(){
		this(false);
	}
	public IntegrationTest(boolean should_initialize){
		if(should_initialize){
			initialize();
		}
		testCases = new ArrayList<TestCase>();
		L = new ArrayList<String>();
		L.add("eval test0 \"(a = 4) & (b)=(5) & (6) = c & (17 = d)\";");
		L.add("eval test1 \"?lsd_2 (a = 4) & (b)=(5) & (6) = c & (17 = d)\";");
		L.add("eval test2 \"?msd_3 (a = 4) & (b)=(5) & (6) = c & (17 = d)\";");
		L.add("eval test3 \"?msd_fib (a = 4) & (b)=(5) & (6) = c & (17 = d)\";");
		L.add("eval test4 \"?lsd_fib (a = 4) & (b)=(5) & (6) = c & (17 = d)\";");
		L.add("eval test5 \"?lsd_trib (a = 4) & (b)=(5) & (6) = c & (17 = d)\";");
		L.add("eval test6 \"(a = 4) & (?msd_3 (b)=(5)) & (6) = c & (17 = d)\";");
		L.add("eval test7 \"(a = 4) & ?msd_3 (b)=(5) & (6) = c & (17 = d)\";");
		L.add("eval test8 \"(a = 4) & (?msd_3 (b)=(5)) & (?lsd_fib (6) = c) & (17 = d)\";");
		L.add("eval test9 \"(a = 4) & (?msd_3 (b)=(5)) & ?lsd_fib (6) = c & (17 = d)\";");
		L.add("eval test10 \"a <= 9 & a!=8 & a <9 & 4 <= a & 6 != a\";");//a = 4,5,7
		L.add("eval test11 \"?msd_fib a <= 9 & a!=8 & a <9 & 4 <= a & 6 != a\";");//a = 4,5,7
		L.add("eval test12 \"?lsd_10 a <= 9 & a!=8 & a <9 & 4 <= a & 6 != a\";");//a = 4,5,7
		L.add("eval test13 \"~(a >= 10 | a < 4) & ~(a = 9 | (a<7 & a>=6)) & a != 8\";");//a = 4,5,7
		L.add("eval test14 \"?msd_fib ~(a >= 10 | a < 4) & ~(a = 9 | (a<7 & a>=6)) & a != 8\";");//a = 4,5,7
		L.add("eval test15 \"?lsd_fib ~(a >= 10 | a < 4) & ~(a = 9 | (a<7 & a>=6)) & a != 8\";");//a = 4,5,7
		L.add("eval test16 \"?lsd_10 ~(a >= 10 | a < 4) & ~(a = 9 | (a<7 & a>=6)) & a != 8\";");//a = 4,5,7
		L.add("eval test17 \"?msd_trib ~(a >= 10 | a < 4) & ~(a = 9 | (a<7 & a>=6)) & a != 8\";");//a = 4,5,7
		L.add("eval test18 \"((a<=5 & a > 3) | a = 7 | a = 9 | a = 45) & a <= 7\";");//a = 4,5,7
		L.add("eval test19 \"?msd_fib ((a<=5 & a > 3) | a = 7 | a = 9 | a = 45) & a <= 7\";");//a = 4,5,7
		L.add("eval test20 \"?lsd_fib ((a<=5 & a > 3) | a = 7 | a = 9 | a = 45) & a <= 7\";");//a = 4,5,7
		L.add("eval test21 \"?lsd_10 ((a<=5 & a > 3) | a = 7 | a = 9 | a = 45) & a <= 7\";");//a = 4,5,7
		L.add("eval test22 \"?msd_10 (a = 12 | 100=a | a = 9) & 10 <= a\";"); //a = 12 , 100
		L.add("eval test23 \"a >= 2 => a<= 3\";");//a = 0,1,2,3
		L.add("eval test24 \"?lsd_fib a >= 2 => a<= 3\";");//a = 0,1,2,3
		L.add("eval test25 \"?msd_10 a < 20 => a<= 3\";");//a >= 20 | a<=3
		L.add("eval test26 \" a =6 ^ a=6\";");
		L.add("eval test27 \"?msd_fib a =6 ^ a=6\";");
		L.add("eval test28 \" a !=6 ^ a=6\";");
		L.add("eval test29 \"?msd_fib a !=6 ^ a=6\";");
		L.add("eval test30 \" a =6 ^ a<7\";");//a = 0,1,2,3,4,5
		L.add("eval test31 \"?msd_fib a =6 ^ a<7\";");//a = 0,1,2,3,4,5
		L.add("eval test32 \" a <=5 <=> ~(a>2)\";");//a = 0,1,2,6,7,8,...
		L.add("eval test33 \"?msd_fib a <=5 <=> ~(a>2)\";");//a = 0,1,2,6,7,8,...
		L.add("eval test34 \"?msd_fib a <=b & a>=b\";");//a=b
		L.add("eval test35 \"?lsd_3 a <=b & a>=b\";");//a=b
		L.add("eval test36 \"?msd_fib a <=a+1\";");
		L.add("eval test37 \"?msd_fib a <=a-1\";");
		L.add("eval test38 \"?msd_fib 2+a < a\";");
		L.add("eval test39 \"?msd_fib a =3*a\";");
		L.add("eval test40 \"?msd_fib 5+2*a = 4*a+1\";");
		L.add("eval test41 \"E a , b, c ,d b = 12 & e =a+2*b-c*3+b-a+d/2-3-2+5*2-8/4 & c <6 & d = 11 & c >= 5\";");//e = 29
		L.add("eval test42 \"?lsd_fib E b, c b = 12 & e =2*b-c/3+b-1 & c <20 & c >= 19\";");//e = 29
		L.add("eval test43 \"E b, c ,d b = 12 & a+2*b-c*3+b-a+d/2-3-2+5*2-8/4=a & c <6 & d = 11 & c >= 5\";");//a = 29

		L.add("eval test44 \"d = 20 & (?msd_fib b = 3) & a = 33 & (?msd_fib c = 4)\";");
		L.add("eval test45 \"Ea d = 20 & (?msd_fib b = 3) & a = 33 & (?msd_fib c = 4)\";");
		L.add("eval test46 \"Ed d = 20 & (?msd_fib b = 3) & a = 33 & (?msd_fib c = 4)\";");
		L.add("eval test47 \"Ed,a d = 20 & (?msd_fib b = 3) & a = 33 & (?msd_fib c = 4)\";");
		L.add("eval test48 \"Ea,d,c d = 20 & (?msd_fib b = 2) & a = 33 & (?msd_fib c = 4)\";");
		L.add("eval test49 \"Eb,d,a d = 20 & (?msd_fib b = 2) & a = 33 & (?msd_fib c = 4)\";");

		L.add("eval test50 \"?lsd_2 d = 20 & (?lsd_fib b = 3) & a = 33 & (?lsd_fib c = 4)\";");
		L.add("eval test51 \"?lsd_2 Ea d = 20 & (?lsd_fib b = 3) & a = 33 & (?lsd_fib c = 4)\";");
		L.add("eval test52 \"?lsd_2 Ed d = 20 & (?lsd_fib b = 3) & a = 33 & (?lsd_fib c = 4)\";");
		L.add("eval test53 \"?lsd_2 Ed,a d = 20 & (?lsd_fib b = 3) & a = 33 & (?lsd_fib c = 4)\";");
		L.add("eval test54 \"?lsd_2 Ea,d,c d = 20 & (?lsd_fib b = 2) & a = 33 & (?lsd_fib c = 4)\";");
		L.add("eval test55 \"?lsd_2 Eb,d,a d = 20 & (?lsd_fib b = 2) & a = 33 & (?lsd_fib c = 4)\";");

		L.add("eval test56 \"~( b != 6 | ?msd_fib a != 17)\";");
		L.add("eval test57 \"~( b != 6 | ?lsd_fib a != 17)\";");
		L.add("eval test58 \"Eb ( b = 6 & ?lsd_fib a = 17)\";");
		L.add("eval test59 \"Ea ( b = 6 & ?lsd_fib a = 17)\";");

		L.add("eval test60 \"Ed (?msd_fib Eb (a = b-2) & b > 4 & b <= 6) & ( Ec (d = c-2) & c > 4 & c <= 6)\";");
		L.add("eval test61 \"?lsd_2 Ea (Eb (a = b-2) & b > 4 & b <= 6) & (?lsd_fib Ec (d = c-2) & c > 4 & c <= 6)\";");

		L.add("eval test62 \"Ea (Eb (a = b-2) & b > 4 & b <= 6) & (?lsd_fib Ec (d = c-2) & c > 4 & c <= 6)\";");

		L.add("eval test63 \"?lsd_2 Ea  b = a-2 & a = 8\";");
		L.add("eval test64 \"Ea ?lsd_2 b = a-2 & a = 8\";");

		L.add("eval test65 \"?lsd_fib Ex,y x < y\";");
		L.add("eval test66 \"Ex,y,z y = 2*x+1 & y = 2*z\";");
		L.add("eval test67 \"?lsd_fib Ex,y,z y = 2*x+1 & y = 2*z\";");
		L.add("eval test68 \"Ex,y,z y = 2*x+1 & y = 3*z\";");
		L.add("eval test69 \"?lsd_fib Ex,y,z y = 2*x+1 & y = 3*z\";");
		L.add("eval test70 \"Ex,y y = 4*x+1 & y = 11\";");
		L.add("eval test71 \"?lsd_fib Ex,y y = 4*x+1 & y = 11\";");
		L.add("eval test72 \"Ex,y y = 4*x+1 & y = 13\";");
		L.add("eval test73 \"?lsd_fib Ex,y y = 4*x+1 & y = 13\";");
		L.add("eval test74 \"Ex 13 = 4*x+1\";");
		L.add("eval test75 \"?lsd_fib Ex 13 = 4*x+1\";");
		L.add("eval test76 \"Ex 11 = 4*x+1\";");
		L.add("eval test77 \"?lsd_fib Ex 11 = 4*x+1\";");

		L.add("eval test78 \"(Ex,y x<y) & (z=3)\";");
		L.add("eval test79 \"(Ex,y x<y) | (z=3)\";");
		L.add("eval test80 \"(Ex,y x<y) ^ (z=3)\";");
		L.add("eval test81 \"(Ex,y x<y) <=> (z=3)\";");
		L.add("eval test82 \"(Ex,y x<y) => (z=3)\";");
		L.add("eval test83 \"~(Ex,y x<y)\";");

		L.add("eval test84 \"(z=3) & (Ex x>x+1)\";");
		L.add("eval test85 \"(z=3) | (Ex x>x+1)\";");
		L.add("eval test86 \"(z=3) ^ (Ex x>x+1)\";");
		L.add("eval test87 \"(z=3) <=> (Ex x>x+1)\";");
		L.add("eval test88 \"(z=3) => (Ex x>x+1)\";");
		L.add("eval test89 \"~(Ex x>x+1)\";");

		L.add("eval test90 \"(Ex x>2*x)&(Ex,y x <y-4)\";");
		L.add("eval test91 \"(Ex x>2*x)|(Ex,y x <y-4)\";");
		L.add("eval test92 \"(Ex x>2*x)^(Ex,y x <y-4)\";");
		L.add("eval test93 \"(Ex x>2*x)<=>(Ex,y x <y-4)\";");
		L.add("eval test94 \"(Ex x>2*x)=>(Ex,y x <y-4)\";");

		L.add("eval test95 \"(Ex,y x <=y)&(Ex x=2 & x = 3)\";");
		L.add("eval test96 \"(Ex,y x <=y)|(Ex x=2 & x = 3)\";");
		L.add("eval test97 \"(Ex,y x <=y)^(Ex x=2 & x = 3)\";");
		L.add("eval test98 \"(Ex,y x <=y)<=>(Ex x=2 & x = 3)\";");
		L.add("eval test99 \"(Ex,y x <=y)=>(Ex x=2 & x = 3)\";");

		L.add("eval test100 \"(Ex 9 = 3*x )&(Ex x = 2 | x = 3)\";");
		L.add("eval test101 \"(Ex 9 = 3*x )|(Ex x = 2 | x = 3)\";");
		L.add("eval test102 \"(Ex 9 = 3*x )^(Ex x = 2 | x = 3)\";");
		L.add("eval test103 \"(Ex 9 = 3*x )<=>(Ex x = 2 | x = 3)\";");
		L.add("eval test104 \"(Ex 9 = 3*x )=>(Ex x = 2 | x = 3)\";");

		L.add("eval test105 \"~(Ex 9 = 3*x )&~(Ex x = 2 | x = 3)\";");
		L.add("eval test106 \"~(Ex 9 = 3*x )|~(Ex x = 2 | x = 3)\";");
		L.add("eval test107 \"~(Ex 9 = 3*x )^~(Ex x = 2 | x = 3)\";");
		L.add("eval test108 \"~(Ex 9 = 3*x )<=>~(Ex x = 2 | x = 3)\";");
		L.add("eval test109 \"~(Ex 9 = 3*x )=>~(Ex x = 2 | x = 3)\";");

		L.add("eval test110 \"?lsd_fib Eb a = b & b = 3\";");
		L.add("eval test111 \"?lsd_fib Eb b != a & b = 3\";");
		L.add("eval test112 \"?lsd_fib Eb a < b & b = 4\";");
		L.add("eval test113 \"?lsd_fib Eb b > a & b = 4\";");
		L.add("eval test114 \"?lsd_fib Eb a <= b & b = 3\";");
		L.add("eval test115 \"?lsd_fib Eb b >= a & b = 3\";");

		L.add("eval test116 \"?lsd_fib `(a = 15)\";");
		L.add("eval test117 \"?lsd_fib ```(a = 15)\";");
		L.add("eval test118 \"`(?lsd_fib (a = 15))\";");

		L.add("eval test119 \"E a (?lsd_fib a = 10 ) & b = a+1\";");
		L.add("eval test120 \"E a (?lsd_fib `(a = 10) ) & b = a+3\";");
		L.add("eval test121 \"E a `(?lsd_fib a = 10 ) & b = a+3\";");
		L.add("eval test122 \"E a ```(?lsd_fib a = 10 ) & b = a+3\";");

		L.add("eval test123 \"E a (?lsd_fib a = 10 ) & `(b = a+5)\";");
		L.add("eval test124 \"E a (?lsd_fib a = 10 ) & ```(b = a+5)\";");
		L.add("eval test125 \"`(E a `(?lsd_fib a = 10 ) & (b = a+5))\";");

		L.add("eval test126 \"?lsd_fib `~``~~`~(a=15)\";");
		L.add("eval test127 \"`~``~~`~(a=15)\";");
		L.add("eval test128 \"?lsd_fib ``~``~~`~(a=15)\";");
		L.add("eval test129 \"``~``~~`~(a=15)\";");
		L.add("eval test130 \" `~``~~`~(a=3)\";");
		L.add("eval test131 \" ~`~``~~`~(a=3)\";");
		L.add("eval test132 \"?msd_fib `~``~~`~(a=3)\";");
		L.add("eval test133 \"?msd_fib ~`~``~~`~(a=3)\";");

		L.add("eval test134 \"Ax  y < x+4\";");
		L.add("eval test135 \"?lsd_fib Ax  y < x+5\";");
		L.add("eval test136 \"Ax  y != 2*x+1\";");
		L.add("eval test137 \"?lsd_2 Au,v  (x != 2*u+1) & (?lsd_3 y != 3*v+2)\";");
		L.add("eval test138 \"Au,v  (x != 2*u+1) & (?msd_3 y != 3*v+2)\";");

		L.add("reg test139 {0,1} \"100*\";");
		L.add("reg     test140   msd_2 \"100*\";");
		L.add("reg test141 {  0  ,   1   ,   2  }  \"100*\";");
		L.add("reg test142 {  0  ,   1   ,   - 2  ,+4,        5   }  \"100*\";"); //error: the input alphabet of an automaton generated from a regular expression must be a subset of {0,1,...,9}
		L.add("reg test143 {  0  ,   1   ,   +  2  ,+4,      +  5   }  \"100*\";");
		L.add("reg test144      msd_fib  \"100*\";");
		L.add("reg test145      lsd_10     \"100*\";");
		L.add("reg test146      fib  \"100*\";");
		L.add("reg test147    2  \"100*\";");
		L.add("reg test148      lsd  \"100*\";");
		L.add("reg test149      lsd  \"100*270*\";");
		L.add("reg test150      lsd  \"100*(271)*\";");
		L.add("reg test151      lsd_3  \"100*(27)?1*\";");
		L.add("reg test152 3 \"100*2?7?1*\";");
		L.add("reg test153 {0,4,6,7} \".[5-6]*[3-6]\";");
		L.add("reg test154 msd_5 \".[5-9]*[8-9].\";");
		L.add("reg test155 msd_5 \".[4-9]+.\";");

		L.add("reg test156 \"T[a]=1\";"); //error: invalid use of reg command
		L.add("eval test157 \"T[a] = T[2*a]\";");
		L.add("eval test158 \"T[a] <= @2\";");
		L.add("eval test159 \"T[a] = T[2*a+1]\";");
		L.add("eval test160 \"T[a] = @0\";");
		L.add("eval test161 \"@1 = T[  a  ]\";");
		L.add("eval test162 \"@-10 = T[a]\";");
		L.add("eval test163 \"T[a] = T[a+1]\";");
		L.add("eval test164 \"Eb T[a] =T[b] & b = a+1\";");
		L.add("eval test165 \"T[a] =T[b] & b = a+1\";");
		L.add("eval test166 \"T[a<=10 & a>=5] = @1\";");
		L.add("eval test167 \"T[a<=10&T[a]=@1]=@1\";");
		L.add("eval test168 \"T[Eb a = b & T[b]>T[2*a+1]]=T[a<=12]\";");
		L.add("eval test169 \"Ak k<n => T[i+k]=T[i+k+n]\";");
		L.add("eval test170 \"Ak k<=n => T[i+k]=T[i+k+n]\";");
		L.add("eval test171 \"n>=1 & Ak k<=n => T[i+k]=T[i+k+n]\";");
		L.add("eval test172 \"En n>= 1 & Ak k< n => T[i+k]=T[i+k+n]\";");
		L.add("eval test173 \"n>0 & Ei Am (m>0 & m <n) => Ek k<m & T[i+k] != T[i+n-m+k]\";");
		L.add("eval test174 \"?msd_fib n > 0 & Ei Ak k<n => F[i+k]=F[i+k+n]\";");
		L.add("eval test175 \"?msd_fib En n > 0 & Ak k<n => F[i+k]=F[i+k+n]\";");
		L.add("eval test176 \"?msd_fib n > 0 & Ak k <n=>F[i+k]=F[i+k+n]\";");
		L.add("eval test177 \"?msd_fib n>0 & Ei Ak k < n => R[i+k]=R[i+k+n]\";");
		L.add("eval test178 \"?lsd_2 n > 0 & Ef,i i >= 1 & $endsIn2Zeros(i) & $endsIn2Zeros(n) & (Ak k < n => PF[f][i+k] = PF[f][i+k+n])\";");
		L.add("eval test179 \"n > 0 & Ef,i i >= 1 & $startsWith2Zeros(i) & $startsWith2Zeros(n) & (Ak k < n => PFmsd[f][i+k] = PFmsd[f][i+k+n])\";");//squares
		L.add("eval test180 \"?lsd_2 n > 0 & Ef,i i >= 1 & $endsIn2Zeros(i) & $endsIn2Zeros(n) & (Ak k < 2*n => PF[f][i+k] = PF[f][i+k+n])\";");//cubes

		L.add("eval test181 \"Ey,w $func(z,x,y,w)\";");
		L.add("eval test182 \"Ez,x,w $func(z,x,y,w)\";");
		L.add("eval test183 \"Ex,y,z $func(z,x,y,w)\";");
		L.add("eval test184 \"Ew,y,x $func(z,x<4 & x>=2,y,w)\";");
		L.add("eval test185 \"Ew,y,z $func(z<5 & z>=3,x,y,w)\";");
		L.add("eval test186 \"Ez,x,y $func(z,x,y,?msd_10 10)\";");
		L.add("eval test187 \"Ez,x,y $func(z,x,y,?msd_10 w=10)\";");
		L.add("eval test188 \"Ez,x,y $func(z,x,y,?msd_10 w=17)\";");
		L.add("eval test189 \"Ez,x,y $func(z,x,y,?msd_10 17)\";");
		L.add("eval test190 \"Ez,x,y $func(z,x,y,17)\";"); // error: in computing cross product of two automaton, variables with the same label must have the same alphabet: char at 8
		L.add("eval test191 \"Ez,x,y $func(z,x,y,?msd_10 Eb (a = b+1))\";");
		L.add("eval test192 \"Ez,x,y $func(z,x,y,`(?lsd_10 Eb a = b+1))\";");
		L.add("eval test193 \"Ez,w,x $func(z,x,?msd_3 y+2,w)\";");
		L.add("eval test194 \"Ez,w,x $func(z,x,?msd_3 y-1,w)\";");
		L.add("eval test195 \"Ez,x,y $func(z,x,y,?msd_10 a+1)\";");

		L.add("eval test196 \"$thueeq(x,y)\";");
		L.add("eval test197 \"$thueeq(x,x)\";");
		L.add("eval test198 \"Ax $thueeq(x,x)\";");
		L.add("eval test199 \"Ex $thueeq(x,x)\";");
		L.add("eval test200 \"Ax,y x=y=>$thueeq(x,y)\";");
		L.add("eval test201 \"(Ax,y x=y=>$thueeq(x,y)) <=> Ax $thueeq(x,x)\";");
		L.add("eval test202 \"T2[x][x]=@1\";");
		L.add("eval test203 \"T2[x][x+1]=@0\";");
		L.add("eval test204 \"Ax T2[x][x]=@1\";");
		L.add("eval test205 \"?msd_17 a=17\";");
		L.add("eval test206 \"?lsd_17 a=17\";");
		L.add("eval test207 \"?msd_17 a=37\";");
		L.add("eval test208 \"?msd_17 a=b\";");
		L.add("eval test209 \"?msd_17 a=b+1\";");

		L.add("eval test210 \"Ej Ai ((i<n) => T[j+i] = T[j+n+i])\";");
		L.add("eval test211 \"Ei Aj (j < n) => (T[i+j] = T[i+n-1-j])\";");
		L.add("eval test212 \"Ej Ai ((i<=n) => T[j+i] = T[j+n+i])\";");
		L.add("eval test213 \"?msd_fib Ei Ak (k < 2*n) => F[i+k]=F[i+n+k]\";");
		L.add("eval test214 \"En Ei (n >= 1) & (Aj (j>= i) => T[j] = T[n+j])\";");
		L.add("eval test215 \"Ej (At (t<n) => (T[i+t] = T[j+n-1-t]))\";");
		L.add("eval test216 \"Ai Ej (At (t<n) => (T[i+t] = T[j+n-1-t]))\";");
		L.add("eval test217 \"An Ai Ej (At (t<n) => (T[i+t] = T[j+n-1-t]))\";");
		L.add("eval test218 \"Ek ((k>i) & (At ((t<n) => (T[i+t] = T[k+t]))))\";");
		L.add("eval test219 \"Ai Ek ((k>i) & (At ((t<n) => (T[i+t] = T[k+t]))))\";");
		L.add("eval test220 \"An Ai Ek ((k>i) & (At ((t<n) => (T[i+t] = T[k+t]))))\";");
		L.add("eval test221 \"Es (s>i)&(s<=i+l)&(Aj (j<n) => (T[i+j]=T[s+j]))\";");
		L.add("eval test222 \"Ai Es (s>i)&(s<=i+l)&(Aj (j<n) => (T[i+j]=T[s+j]))\";");
		L.add("eval test223 \"El Ai Es (s>i)&(s<=i+l)&(Aj (j<n) => (T[i+j]=T[s+j]))\";");
		L.add("eval test224 \"An El Ai Es (s>i)&(s<=i+l)&(Aj (j<n) => (T[i+j]=T[s+j]))\";");
		L.add("eval test225 \"Ei ( Aj (((j>=1)&((2*j)<=n)) => (Et (t < j) & (T[i+t] != T[i+n-j+t]))))\";");
		L.add("eval test226 \"El As Ar ((l<=r)&(r<=s)&(s<=l+n-1)) => (( (Ai (i+r<=s) => T[r+i]=T[s-i]) & (Au ((l<=u)&(u<r)) => (Ej (j+u<=s) & T[u+j] != T[s-j]))) => (Ah ((l<=h)&(h<r)) => (Ek (k+r<=s) & T[h+k] != T[r+k])))\";");
		L.add("eval test227 \"?msd_fib An Ej (j<=n)&(j<n+p)&(Ak (k<p) => F[k] = F[k+p])\";");
		L.add("eval test228 \"Ei (Aj (j<n) => (T[i+j] != T[i+j+n]))\";");
		L.add("eval test229 \"Ei Ej (Ak (k<n) => (T[i+k] = RS[j+k]))\";");
		L.add("eval test230 \"Ei At ((t<n) => ((T[i+t]=T[i+t+n]) & (T[i+t]=T[i+3*n-1-t])))\";");
		L.add("eval test231 \"?msd_fib Ei Ej (j=i+2*n) & (At (t<n) =>(R[i+t]=R[i+t+n])) & (At (t<n) => (R[j+t]=R[j-1-t]))\";");
		L.add("eval test232 \"Ei $thuepriv(i,n)\";");

		L.add("eval test233 \"(m<=n) & (Ek (k+m<=n) & $thue_factoreq(i,j+k,m))\";");
		L.add("eval test234 \"$thue_in(m,1,n) & $thue_factoreq(i,i+n-m,m)\";");
		L.add("eval test235 \"Am $thue_in(m,1,n) => (Ej $thue_subs(j,i,1,m) & $thue_pal(j,i+m-j) & ~$thue_occurs(j,i,i+m-j,m-1))\";");
		L.add("eval test236 \"$thue_priv(i,n) & (Aj (j<i) => ~$thue_factoreq(i,j,n))\";");
		L.add("eval test237 \"$thue_priv(i,n) & $thue_pal(i,n)\";");
		L.add("eval test238 \"$thue_privpal(i,n) & (Aj (j<i) => ~$thue_factoreq(i,j,n))\";");
		L.add("eval test239 \"(n<=1) | (Ej (j<n)& $thue_border(i,j,n) & ~$thue_occurs(i,i+1,j,n-2))\";");
		L.add("eval test240 \"$thue_closed(i,n) & ~$thue_occurs(i,0,n,i+n-1)\";");
		L.add("eval test241 \"Ei $thue_closed(i,n)\";");
		L.add("eval test242 \"$thue_pal(i,n) & (Aj ((j>=1)&$thue_factoreq(i,j,n)) => (T[j-1] != T[j+n]))\";");
		L.add("eval test243 \"$thue_subs(i,j,m,n-1) & (Er $thue_subs(r,j,m,n-1) & $thue_factoreq(i,r,m) & T[r+m]=@0) & (Es $thue_subs(s,j,m,n-1) & $thue_factoreq(i,s,m) & T[s+m] = @1)\";");
		L.add("eval test244 \"Ei $thue_rtspec(i,j,p,n)\";");
		L.add("eval test245 \"Er Es ($thue_subs(r,j,p+1,n) & $thue_subs(s,j,p+1,n) & $thue_factoreq(r,s,p) & T[s+p] != T[r+p])\";");
		L.add("eval test246 \"~$thue_rt(j,n,p) & (Ac (~$thue_rt(j,n,c)) => c >=p)\";");
		L.add("eval test247 \"~$thue_rt2(j,n,p) & (Ac (~$thue_rt2(j,n,c)) => c >=p)\";");
		L.add("eval test248 \"~$thue_occurs(j+n-q,j,q,n-1)\";");
		L.add("eval test249 \"$thue_unrepsuf(j,n,q) & (Ac $thue_unrepsuf(j,n,c) => (c >= q))\";");
		L.add("eval test250 \"(n<=1) | (Ep Eq (n=p+q) & $thue_minunrepsuf(j,n,p) & $thue_minrt(j,n,q))\";");
		L.add("eval test251 \"(n<=1) | (Ep Eq (n=p+q) & $thue_minunrepsuf(j,n,p) & $thue_minrt2(j,n,q))\";");
		L.add("eval test252 \"Em (m+2 <= n) & Ej Ek ($thue_subs(j,i+1,m,n-2) & $thue_subs(k,i+1,m,n-2) & $thue_pal(j,m) & $thue_factoreq(j,k,m) & (T[j-1]=T[j+m]) & (T[k-1]=T[k+m]) & (T[j-1] != T[k-1]))\";");
		L.add("eval test253 \"Em (m >= 2) & (Ej Ek ($thue_subs(j,i,m,n) & $thue_subs(k,i,m,n) & $thue_pal(j,m) & $thue_pal(k,m) & $thue_factoreq(j+1,k+1,m-2) & T[j]!=T[k]))\";");
		L.add("eval test254 \"Ei $thue_rich(i,n)\";");
		L.add("eval test255 \"Ei $thue_priv(i,n)\";");
		L.add("eval test256 \"Ei $thue_maxpal(i,n)\";");
		L.add("eval test257 \"Ej $thue_trap(j,n)\";");
		L.add("eval test258 \"Ej ~$thue_unbal(j,n)\";");

		L.add("eval test259 \"Ak (k<n) => RS[i+k]=RS[j+k]\";");
		L.add("eval test260 \"Ak (k<n) => RS[i+k] = RS[i+n-1-k]\";");
		L.add("eval test261 \"(m<=n) & (Ek (k+m<=n) & $rudin_factoreq(i,j+k,m))\";");
		L.add("eval test262 \"$rudin_in(m,1,n) & $rudin_factoreq(i,i+n-m,m)\";");
		L.add("eval test263 \"Am $rudin_in(m,1,n) => (Ej $rudin_subs(j,i,1,m) & $rudin_pal(j,i+m-j) & ~$rudin_occurs(j,i,i+m-j,m-1))\";");
		L.add("eval test264 \"Ei $rudin_rich(i,n)\";");
		L.add("eval test265 \"Aj $rudin_in(j,1,n-m-1) => ~$rudin_factoreq(i,i+j,m)\";");
		L.add("eval test266 \"Aj $rudin_in(j,1,n-m-1) => ~$rudin_factoreq(i+n-m,i+n-m-j,m)\";");
		L.add("eval test267 \"(n<=1) | (Am $rudin_in(m,1,n) => (Ep $rudin_in(p,1,m) & ($rudin_border(i,p,n) & $rudin_uniqpref(i,p,m) & $rudin_uniqsuff(i+n-m,p,m))))\";");
		L.add("eval test268 \"Ei $rudin_priv(i,n)\";");
		L.add("eval test269 \"(n<=1) | (Ej (j<n)& $rudin_border(i,j,n) & ~$rudin_occurs(i,i+1,j,n-2))\";");
		L.add("eval test270 \"$rudin_closed(i,n) & ~$rudin_occurs(i,0,n,i+n-1)\";");
		L.add("eval test271 \"Ei $rudin_closed(i,n)\";");
		L.add("eval test272 \"$rudin_pal(i,n) & (Aj ((j>=1)&$rudin_factoreq(i,j,n)) => (RS[j-1] != RS[j+n]))\";");
		L.add("eval test273 \"Ei $rudin_maxpal(i,n)\";");
		L.add("eval test274 \"Er Es ($rudin_subs(r,j,p+1,n) & $rudin_subs(s,j,p+1,n) & $rudin_factoreq(r,s,p) & RS[s+p] != RS[r+p])\";");
		L.add("eval test275 \"~$rudin_rt2(j,n,p) & (Ac (~$rudin_rt2(j,n,c)) => c >=p)\";");
		L.add("eval test276 \"~$rudin_occurs(j+n-q,j,q,n-1)\";");
		L.add("eval test277 \"$rudin_unrepsuf(j,n,q) & (Ac $rudin_unrepsuf(j,n,c) => (c >= q))\";");
		L.add("eval test278 \"(n<=1) | (Ep Eq (n=p+q) & $rudin_minunrepsuf(j,n,p) & $rudin_minrt2(j,n,q))\";");
		L.add("eval test279 \"Ej $rudin_trap2(j,n)\";");
		L.add("eval test280 \"Em (m+2 <= n) & Ej Ek ($rudin_subs(j,i+1,m,n-2) & $rudin_subs(k,i+1,m,n-2) & $rudin_pal(j,m) & $rudin_factoreq(j,k,m) & (RS[j-1]=RS[j+m]) & (RS[k-1]=RS[k+m]) & (RS[j-1] != RS[k-1]))\";");
		L.add("eval test281 \"Em (m >= 2) & (Ej Ek ($rudin_subs(j,i,m,n) & $rudin_subs(k,i,m,n) & $rudin_pal(j,m) & $rudin_pal(k,m) & $rudin_factoreq(j+1,k+1,m-2) & RS[j]!=RS[k]))\";");
		L.add("eval test282 \"Ej ~$rudin_unbal(j,n)\";");

		L.add("eval test283 \"?lsd_2 (j<=i) & (i+m<=j+n)\";");
		L.add("eval test284 \"?lsd_2 Ak (k<n) => RS[i+k]=RS[j+k]\";");
		L.add("eval test285 \"?lsd_2 Ak (k<n) => RS[i+k] = RS[i+n-1-k]\";");
		L.add("eval test286 \"?lsd_2 (m<=n) & (Ek (k+m<=n) & $rudin_trapezoid_factoreq(i,j+k,m))\";");
		L.add("eval test287 \"?lsd_2 Er Es ($rudin_trapezoid_subs(r,j,p+1,n) & $rudin_trapezoid_subs(s,j,p+1,n) & $rudin_trapezoid_factoreq(r,s,p) & RS[s+p] != RS[r+p])\";");
		L.add("eval test288 \"?lsd_2 ~$rudin_trapezoid_rt2(j,n,p) & (Ac (~$rudin_trapezoid_rt2(j,n,c)) => c >=p)\";");
		L.add("eval test289 \"?lsd_2 ~$rudin_trapezoid_occurs(j+n-q,j,q,n-1)\";");
		L.add("eval test290 \"?lsd_2 $rudin_trapezoid_unrepsuf(j,n,q) & (Ac $rudin_trapezoid_unrepsuf(j,n,c) => (c >= q))\";");
		L.add("eval test291 \"?lsd_2 (n<=1) | (Ep Eq (n=p+q) & $rudin_trapezoid_minunrepsuf(j,n,p) & $rudin_trapezoid_minrt2(j,n,q))\";");
		L.add("eval test292 \"?lsd_2 Ej $rudin_trapezoid_trap2(j,n)\";");

		L.add("eval test293 \"Ak (k<n) => P[i+k]=P[j+k]\";");
		L.add("eval test294 \"Ak (k<n) => P[i+k] = P[i+n-1-k]\";");
		L.add("eval test295 \"(m<=n) & (Ek (k+m<=n) & $paperfolding_factoreq(i,j+k,m))\";");
		L.add("eval test296 \"$paperfolding_in(m,1,n) & $paperfolding_factoreq(i,i+n-m,m)\";");
		L.add("eval test297 \"Am $paperfolding_in(m,1,n) => (Ej $paperfolding_subs(j,i,1,m) & $paperfolding_pal(j,i+m-j) & ~$paperfolding_occurs(j,i,i+m-j,m-1))\";");
		L.add("eval test298 \"Ei $paperfolding_rich(i,n)\";");
		L.add("eval test299 \"Aj $paperfolding_in(j,1,n-m-1) => ~$paperfolding_factoreq(i,i+j,m)\";");
		L.add("eval test300 \"Aj $paperfolding_in(j,1,n-m-1) => ~$paperfolding_factoreq(i+n-m,i+n-m-j,m)\";");
		L.add("eval test301 \"(n<=1) | (Am $paperfolding_in(m,1,n) => (Ep $paperfolding_in(p,1,m) & ($paperfolding_border(i,p,n) & $paperfolding_uniqpref(i,p,m) & $paperfolding_uniqsuff(i+n-m,p,m))))\";");
		L.add("eval test302 \"Ei $paperfolding_priv(i,n)\";");
		L.add("eval test303 \"(n<=1) | (Ej (j<n)& $paperfolding_border(i,j,n) & ~$paperfolding_occurs(i,i+1,j,n-2))\";");
		L.add("eval test304 \"$paperfolding_closed(i,n) & ~$paperfolding_occurs(i,0,n,i+n-1)\";");
		L.add("eval test305 \"Ei $paperfolding_closed(i,n)\";");
		L.add("eval test306 \"$paperfolding_pal(i,n) & (Aj ((j>=1)&$paperfolding_factoreq(i,j,n)) => (P[j-1] != P[j+n]))\";");
		L.add("eval test307 \"Ei $paperfolding_maxpal(i,n)\";");
		L.add("eval test308 \"Em (m+2 <= n) & Ej Ek ($paperfolding_subs(j,i+1,m,n-2) & $paperfolding_subs(k,i+1,m,n-2) & $paperfolding_pal(j,m) & $paperfolding_factoreq(j,k,m) & (P[j-1]=P[j+m]) & (P[k-1]=P[k+m]) & (P[j-1] != P[k-1]))\";");
		L.add("eval test310 \"Ej ~$paperfolding_unbal(j,n)\";");

		L.add("eval test311 \"?lsd_2 (j<=i) & (i+m<=j+n)\";");
		L.add("eval test312 \"?lsd_2 Ak (k<n) => PR[i+k]=PR[j+k]\";");
		L.add("eval test313 \"?lsd_2 Ak (k<n) => PR[i+k] = PR[i+n-1-k]\";");
		L.add("eval test314 \"?lsd_2 (m<=n) & (Ek (k+m<=n) & $paperfolding_trapezoidal_factoreq(i,j+k,m))\";");
		L.add("eval test315 \"?lsd_2 Er Es ($paperfolding_trapezoidal_subs(r,j,p+1,n) & $paperfolding_trapezoidal_subs(s,j,p+1,n) & $paperfolding_trapezoidal_factoreq(r,s,p) & PR[s+p] != PR[r+p])\";");
		L.add("eval test316 \"?lsd_2 ~$paperfolding_trapezoidal_rt2(j,n,p) & (Ac (~$paperfolding_trapezoidal_rt2(j,n,c)) => c >=p)\";");
		L.add("eval test317 \"?lsd_2 ~$paperfolding_trapezoidal_occurs(j+n-q,j,q,n-1)\";");
		L.add("eval test318 \"?lsd_2 $paperfolding_trapezoidal_unrepsuf(j,n,q) & (Ac $paperfolding_trapezoidal_unrepsuf(j,n,c) => (c >= q))\";");
		L.add("eval test319 \"?lsd_2 (n<=1) | (Ep Eq (n=p+q) & $paperfolding_trapezoidal_minunrepsuf(j,n,p) & $paperfolding_trapezoidal_minrt2(j,n,q))\";");
		L.add("eval test320 \"?lsd_2 Ej $paperfolding_trapezoidal_trap2(j,n)\";");

		L.add("eval test320 \"Ak (k<n) => PD[i+k]=PD[j+k]\";");
		L.add("eval test321 \"Ak (k<n) => PD[i+k] = PD[i+n-1-k]\";");
		L.add("eval test322 \"(m<=n) & (Ek (k+m<=n) & $period_doubling_factoreq(i,j+k,m))\";");
		L.add("eval test323 \"$period_doubling_in(m,1,n) & $period_doubling_factoreq(i,i+n-m,m)\";");
		L.add("eval test324 \"Am $period_doubling_in(m,1,n) => (Ej $period_doubling_subs(j,i,1,m) & $period_doubling_pal(j,i+m-j) & ~$period_doubling_occurs(j,i,i+m-j,m-1))\";");
		L.add("eval test325 \"Ei $period_doubling_rich(i,n)\";");
		L.add("eval test326 \"Ai An $period_doubling_rich(i,n)\";");
		L.add("eval test327 \"Aj $period_doubling_in(j,1,n-m-1) => ~$period_doubling_factoreq(i,i+j,m)\";");
		L.add("eval test328 \"Aj $period_doubling_in(j,1,n-m-1) => ~$period_doubling_factoreq(i+n-m,i+n-m-j,m)\";");
		L.add("eval test329 \"(n<=1) | (Am $period_doubling_in(m,1,n) => (Ep $period_doubling_in(p,1,m) & ($period_doubling_border(i,p,n) & $period_doubling_uniqpref(i,p,m) & $period_doubling_uniqsuff(i+n-m,p,m))))\";");
		L.add("eval test330 \"Ei $period_doubling_priv(i,n)\";");
		L.add("eval test331 \"(n<=1) | (Ej (j<n)& $period_doubling_border(i,j,n) & ~$period_doubling_occurs(i,i+1,j,n-2))\";");
		L.add("eval test332 \"$period_doubling_closed(i,n) & ~$period_doubling_occurs(i,0,n,i+n-1)\";");
		L.add("eval test333 \"Ei $period_doubling_closed(i,n)\";");
		L.add("eval test334 \"$period_doubling_pal(i,n) & (Aj ((j>=1)&$period_doubling_factoreq(i,j,n)) => (PD[j-1] != PD[j+n]))\";");
		L.add("eval test335 \"Ei $period_doubling_maxpal(i,n)\";");
		L.add("eval test336 \"$period_doubling_subs(i,j,m,n-1) & (Er $period_doubling_subs(r,j,m,n-1) & $period_doubling_factoreq(i,r,m) & PD[r+m]=@0) & (Es $period_doubling_subs(s,j,m,n-1) & $period_doubling_factoreq(i,s,m) & PD[s+m] = @1)\";");
		L.add("eval test337 \"Ei $period_doubling_rtspec(i,j,p,n)\";");
		L.add("eval test338 \"~$period_doubling_rt(j,n,p) & (Ac (~$period_doubling_rt(j,n,c)) => (c >=p))\";");
		L.add("eval test339 \"Er Es ($period_doubling_subs(r,j,p+1,n) & $period_doubling_subs(s,j,p+1,n) & $period_doubling_factoreq(r,s,p) & T[s+p] != T[r+p])\";");
		L.add("eval test340 \"~$period_doubling_rt2(j,n,p) & (Ac (~$period_doubling_rt2(j,n,c)) => (c >=p))\";");
		L.add("eval test341 \"~$period_doubling_occurs(j+n-q,j,q,n-1)\";");
		L.add("eval test342 \"$period_doubling_unrepsuf(j,n,q) & (Ac $period_doubling_unrepsuf(j,n,c) => (c >= q))\";");
		L.add("eval test343 \"(n <=1) | (Ep Eq (n=p+q) & $period_doubling_minunrepsuf(j,n,p) & $period_doubling_minrt(j,n,q))\";");
		L.add("eval test344 \"Ej $period_doubling_trap(j,n)\";");
		L.add("eval test345 \"Em (m+2 <= n) & Ej Ek ($period_doubling_subs(j,i+1,m,n-2) & $period_doubling_subs(k,i+1,m,n-2) & $period_doubling_pal(j,m) & $period_doubling_factoreq(j,k,m) & (PD[j-1]=PD[j+m]) & (PD[k-1]=PD[k+m]) & (PD[j-1] != PD[k-1]))\";");
		L.add("eval test346 \"Em (m >= 2) & (Ej Ek ($period_doubling_subs(j,i,m,n) & $period_doubling_subs(k,i,m,n) & $period_doubling_pal(j,m) & $period_doubling_pal(k,m) & $period_doubling_factoreq(j+1,k+1,m-2) & T[j]!=T[k]))\";");
		L.add("eval test347 \"Ej ~$period_doubling_unbal(j,n)\";");

		L.add("eval test348 \"?msd_fib Ak (k<n) => F[i+k]=F[j+k]\";");
		L.add("eval test349 \"?msd_fib Ak (k<n) => F[i+k] = F[i+n-1-k]\";");
		L.add("eval test350 \"?msd_fib (m<=n) & (Ek (k+m<=n) & $fibonacci_factoreq(i,j+k,m))\";");
		L.add("eval test351 \"?msd_fib $fibonacci_in(m,1,n) & $fibonacci_factoreq(i,i+n-m,m)\";");
		L.add("eval test352 \"?msd_fib Am $fibonacci_in(m,1,n) => (Ej $fibonacci_subs(j,i,1,m) & $fibonacci_pal(j,i+m-j) & ~$fibonacci_occurs(j,i,i+m-j,m-1))\";");
		L.add("eval test353 \"?msd_fib Ei $fibonacci_rich(i,n)\";");
		L.add("eval test354 \"?msd_fib Ai An $fibonacci_rich(i,n)\";");
		L.add("eval test355 \"?msd_fib (n<=1) | (Am $fibonacci_in(m,1,n) => (Ep $fibonacci_in(p,1,m) & $fibonacci_border(i,p,n) & ~$fibonacci_occurs(i,i+1,p,m-1) & ~$fibonacci_occurs(i,i+n-m,p,m-1)))\";");
		L.add("eval test356 \"?msd_fib Ei $fibonacci_priv(i,n)\";");
		L.add("eval test357 \"?msd_fib (n<=1) | (Ej (j<n)& $fibonacci_border(i,j,n) & ~$fibonacci_occurs(i,i+1,j,n-2))\";");
		L.add("eval test358 \"?msd_fib $fibonacci_closed(i,n) & ~$fibonacci_occurs(i,0,n,i+n-1)\";");
		L.add("eval test359 \"?msd_fib Ei $fibonacci_closed(i,n)\";");
		L.add("eval test360 \"?msd_fib $fibonacci_pal(i,n) & (Aj ((j>=1)&$fibonacci_factoreq(i,j,n)) => (F[j-1] != F[j+n]))\";");
		L.add("eval test361 \"?msd_fib Ei $fibonacci_maxpal(i,n)\";");
		L.add("eval test362 \"?msd_fib $fibonacci_subs(i,j,m,n-1) & (Er $fibonacci_subs(r,j,m,n-1) & $fibonacci_factoreq(i,r,m) & F[r+m]=@0) & (Es $fibonacci_subs(s,j,m,n-1) & $fibonacci_factoreq(i,s,m) & F[s+m] = @1)\";");
		L.add("eval test363 \"?msd_fib Ei $fibonacci_rtspec(i,j,p,n)\";");
		L.add("eval test364 \"?msd_fib (~$fibonacci_rt(j,n,p)) & (Ac (~$fibonacci_rt(j,n,c)) => (c >= p))\";");
		L.add("eval test365 \"?msd_fib ~$fibonacci_occurs(j+n-q,j,q,n-1)\";");
		L.add("eval test366 \"?msd_fib $fibonacci_unrepsuf(j,n,q) & (Ac $fibonacci_unrepsuf(j,n,c) => (c >= q))\";");
		L.add("eval test367 \"?msd_fib (Ep Eq (n=p+q) & $fibonacci_minunrepsuf(j,n,p) & $fibonacci_minrt(j,n,q))\";");
		L.add("eval test368 \"?msd_fib Ej  $fibonacci_trap(j,n)\";");
		L.add("eval test369 \"?msd_fib Em (m+2 <= n) & Ej Ek ($fibonacci_subs(j,i+1,m,n-2) & $fibonacci_subs(k,i+1,m,n-2) & $fibonacci_pal(j,m) & $fibonacci_factoreq(j,k,m) & (F[j-1]=F[j+m]) & (F[k-1]=F[k+m]) & (F[j-1] != F[k-1]))\";");
		L.add("eval test370 \"Em (m >= 2) & (Ej Ek ($fibonacci_subs(j,i,m,n) & $fibonacci_subs(k,i,m,n) & $fibonacci_pal(j,m) & $fibonacci_pal(k,m) & $fibonacci_factoreq(j+1,k+1,m-2) & F[j]!=F[k]))\";");
		L.add("eval test371 \"?msd_fib Ej ~$fibonacci_unbal(j,n)\";");
		L.add("eval test372 \"?msd_fib Ej En ~$fibonacci_unbal(j,n)\";");

		// matrix calculation tests
		L.add("eval test373 n j \"i=j+1\";");// error: incidence matrices for the variable n cannot be calculated, because n is not a free variable. : eval test373 n j "i=j+1";
		L.add("eval test374 i j \"i=j+1\";");
		L.add("eval test375 i n \"?msd_fib Aj j<i => (Ek k<n & F[j+k]!=F[i+k])\"::");
		L.add("eval test376 i      length_abc \"?msd_fib Aj j<i => (Ek k<length_abc & F[j+k]!=F[i+k])\"::");
		L.add("eval test377     length_abc               \"?msd_fib Aj j<i => (Ek k<length_abc & F[j+k]!=F[i+k])\"     ::");
		L.add("def test378 n \"?msd_fib (j >= 1) & (i+2*j <= n) & (Ak k<j => F[i+k]=F[i+j+k])\"::");
		L.add("def test379 n \"?msd_fib ($fibmr(i,n,n+1) & ~$fibmr(i,n-1,n))\"::");
		L.add("eval test380 23 \"n23 = 10\"::");// error: invalid use of eval/def command: eval test380 23 "n23 = 10"::
		L.add("eval test381 n23 \"En23 n23 = 10\"::");// error
		L.add("eval test382 n23 \"En23 n23 = 10 & i = 12\"::");//error
		L.add("eval test383 n23 \"Ei n23 = 10 & i = 12\"::");

		// test macro
		L.add("eval test384 \"#palindrome(msd_2,T)\";");
		L.add("eval test385 \"#palindrome(msd_fib,F)\";");
		L.add("eval test386 \"#palindrome(msd_2,RS)\";");
		L.add("eval test387 \"#palindrome(lsd_2,RS)\";");
		L.add("eval test388 \"#palindrome(msd_2,P)\";");
		L.add("eval test389 \"#border(msd_2,thue)\";");
		L.add("eval test390 \"#border(msd_fib,fibonacci)\";");
		L.add("eval test391 \"#border(msd_2,rudin)\";");
		L.add("eval test392 \"#border(msd_2,paperfolding)\";");

		// eval tests based on morphism and image commands
		L.add("eval test393 \"Ai,j,n (n>=3) => ~$fsrevchk(i,j,n)\";");
		L.add("eval test394 \"~Ep,n (p>=1) & (Ai (i>=n) => FS[i]=FS[i+p])\";");
		L.add("eval test395 \"An n>=2 => ~(Ei $gamard6allconj(i,n))\";");
		L.add("eval test396 \"An n>=3 => ~(Ei $gamard3allconj(i,n))\";");
		L.add("eval test397 \"Ai WSA[i]=@0 <=> (Ex $power2(x) & (i+2=5*x|i+2=7*x))\";");

		// test negative numbers used in non-negative bases
		L.add("eval test398 \"a + _1 = 0\";");
		L.add("eval test399 \"a > _1 & a < 1\";");
		L.add("eval test400 \"a < _1\";");
		L.add("eval test401 \"_1-b = a\";");
		L.add("eval test402 \"a + _2*b = 0\";");
		L.add("eval test403 \"a + b/_2 = 0\";");

		// test negative bases
		L.add("eval test404 \"?msd_neg_2 a = _5\";");
		L.add("eval test405 \"?msd_neg_2 a = 5\";");
		L.add("eval test406 \"?msd_neg_2 a = b/2\";");
		L.add("eval test407 \"?lsd_neg_2 a = _5\";");
		L.add("eval test408 \"?lsd_neg_2 a = 5\";");
		L.add("eval test409 \"?lsd_neg_2 a = b/2\";");
		L.add("eval test410 \"?msd_neg_2 a = _b/2\";");
		L.add("eval test411 \"?msd_neg_2 a = b/_5\";");
		L.add("eval test412 \"?msd_neg_2 a + _5 = _5\";");
		L.add("eval test413 \"?msd_neg_2 _a + 2 = 0\";");
		L.add("eval test414 \"?msd_neg_2 _2*_a = 6\";");

		// negafibonacci
		L.add("eval test415 \"?msd_neg_fib (a = 4) & (b)=(5) & (6) = c & (17 = d)\";");
		L.add("eval test416 \"?lsd_neg_fib (a = 4) & (b)=(5) & (6) = c & (17 = d)\";");
		L.add("eval test417 \"?msd_neg_fib a <= 9 & a!=8 & a <9 & 4 <= a & 6 != a\";");//a = 4,5,7
		L.add("eval test418 \"?msd_neg_fib ~(a >= 10 | a < 4) & ~(a = 9 | (a<7 & a>=6)) & a != 8\";");//a = 4,5,7
		L.add("eval test419 \"?lsd_neg_fib ~(a >= 10 | a < 4) & ~(a = 9 | (a<7 & a>=6)) & a != 8\";");//a = 4,5,7
		L.add("eval test420 \"?msd_neg_fib ((a<=5 & a > 3) | a = 7 | a = 9 | a = 45) & a <= 7\";");//a = 4,5,7
		L.add("eval test421 \"?lsd_neg_fib ((a<=5 & a > 3) | a = 7 | a = 9 | a = 45) & a <= 7\";");//a = 4,5,7
		L.add("eval test422 \"?lsd_neg_fib a >= 2 => a<= 3\";");//a <= 3
		L.add("eval test423 \"?msd_neg_fib a =6 ^ a=6\";");
		L.add("eval test424 \"?msd_neg_fib a !=6 ^ a=6\";");
		L.add("eval test425 \"?msd_neg_fib a =6 ^ a<7\";");//a <= 5
		L.add("eval test426 \"?msd_neg_fib a <=5 <=> ~(a>2)\";");//a <= 2 or a >= 6
		L.add("eval test427 \"?msd_neg_fib a <=b & a>=b\";");//a = b
		L.add("eval test428 \"?msd_neg_fib a <=a+1\";");
		L.add("eval test429 \"?msd_neg_fib a <=a-1\";");
		L.add("eval test430 \"?msd_neg_fib 2+a < a\";");
		L.add("eval test431 \"?msd_neg_fib a =3*a\";");
		L.add("eval test432 \"?msd_neg_fib 5+2*a = 4*a+1\";");
		L.add("eval test433 \"?lsd_neg_fib Ex,y x < y\";");
		L.add("eval test434 \"?lsd_neg_fib Ex,y,z y = 2*x+1 & y = 2*z\";");
		L.add("eval test435 \"?lsd_neg_fib Ex,y,z y = 2*x+1 & y = 3*z\";");
		L.add("eval test436 \"?lsd_neg_fib Ex,y y = 4*x+1 & y = 11\";");
		L.add("eval test437 \"?lsd_neg_fib Ex,y y = 4*x+1 & y = 13\";");
		L.add("eval test438 \"?lsd_neg_fib Ex 13 = 4*x+1\";");
		L.add("eval test439 \"?lsd_neg_fib Ex 11 = 4*x+1\";");

		// split, reverseSplit and join
		L.add("split test440 T2[+][+];");
		L.add("split test441 T2[+][-];");
		L.add("split test442 T2[-][+];");
		L.add("split test443 T2[-][-];");
		L.add("rsplit test444[+][+] test440;");
		L.add("rsplit test445[+][-] test441;");
		L.add("rsplit test446[-][+] test442;");
		L.add("rsplit test447[-][-] test443;");
		L.add("join test448 test444[a][b] test445[a][b] test446[a][b] test447[a][b];");
		L.add("split test449 T2[+][];");
		L.add("rsplit test450[+][] T2;");
		L.add("join test451 T[a] T2[a][b];");

		// double variable tests
		L.add("eval test452 \"x + x = 0\";");
		L.add("eval test453 \"x - x = 0\";");
		L.add("eval test454 \"x = x\";");

		// dfao arithmetic tests
		L.add("eval test455 \"T[a] + 5 = 6\";");
		L.add("eval test456 \"?msd_neg_2 T[a] - 5 = _4\";");
		L.add("eval test457 \"T[a] * 5 = 5\";");
		L.add("eval test458 \"TH[a] / 3 = 1\";");
		L.add("eval test459 \"3 / TH[a] = 1\";"); // error: division by zero
		L.add("eval test460 \"T[a] + b = 1\";");
		L.add("eval test461 \"a - (T[a] + b) = 0\";");
		L.add("eval test462 \"?msd_neg_2 T[a] - b = 1\";");
		L.add("eval test463 \"?msd_neg_2 _T[a] = _1\";");


		L.add("eval test464 \"T[a] + (b + c) = 1\";");
		L.add("eval test465 \"?msd_neg_2 T[a] - (b + c) = 1\";");
		L.add("eval test466 \"T[a] * (b + c) = 1\";");
		L.add("eval test467 \"?msd_neg_2 (b + c) / TEST[a] = 1\";");
		L.add("eval test468 \"T[a<5] + (b + c) = 1\";");
		L.add("eval test469 \"?msd_neg_2 T[a<5] - (b + c) = 1\";");
		L.add("eval test470 \"T[a<5] * (b + c) = 1\";");
		L.add("eval test471 \"?msd_neg_2 (b + c) / TEST[a<5] = 1\";");
		L.add("eval test472 \"T[a+d] + (b + c) = 1\";");
		L.add("eval test473 \"?msd_neg_2 T[a+d] - (b + c) = 1\";");
		L.add("eval test474 \"T[a+d] * (b + c) = 1\";");
		L.add("eval test475 \"?msd_neg_2 (b + c) / TEST[a+d] = 1\";");
		L.add("eval test476 \"TH[a] / (b + c) = 1\";"); // error: constants cannot be divided by variables


		L.add("eval test477 \"T[a] < b\";");
		L.add("eval test478 \"T[a] + b > a\";");
		L.add("eval test479 \"T[a] < b + c\";");
		L.add("eval test480 \"?msd_neg_2 T[a] > b + c\";");
		L.add("eval test481 \"T[a] < T[b]\";");
		L.add("eval test482 \"T[a < 5] < b\";");
		L.add("eval test483 \"T[a < 5] + b > a\";");
		L.add("eval test484 \"T[a < 5] < b + c\";");
		L.add("eval test485 \"?msd_neg_2 T[?msd_neg_2 a < 5] > b + c\";");
		L.add("eval test486 \"T[a < 5] < T[b > 5]\";");
		L.add("eval test487 \"T[a + c] < b\";");
		L.add("eval test488 \"T[a + c] + b > a\";");
		L.add("eval test489 \"T[a + d] < b + c\";");
		L.add("eval test490 \"?msd_neg_2 T[?msd_neg_2 a + d] > b + c\";");
		L.add("eval test491 \"T[a + c] < T[b - d]\";");


		L.add("eval test492 \"TH[a] + TH[b] = 0\";");
		L.add("eval test493 \"TH[a] - TH[b] = 0\";");
		L.add("eval test494 \"TH[a] * TH[b] = 4\";");
		L.add("eval test495 \"?msd_neg_2 TH[a] / TEST[b] = _2\";");
		L.add("eval test496 \"?msd_neg_2 TH[a] / TEST[b] = 2\";");
		L.add("eval test497 \"TH[a] = TH[b]\";");
		L.add("eval test498 \"T[a] <= T[b]\";");
		L.add("eval test499 \"TH[a<5] + TH[b>5] = 0\";");
		L.add("eval test500 \"TH[a<5] - TH[b>5] = 0\";");
		L.add("eval test501 \"TH[a<5] * TH[b>5] = 4\";");
		L.add("eval test502 \"?msd_neg_2 TH[a<5] / TEST[b>5] = _2\";");
		L.add("eval test503 \"?msd_neg_2 TH[a<5] / TEST[b>5] = 2\";");
		L.add("eval test504 \"TH[a<5] = TH[b>5]\";");
		L.add("eval test505 \"T[a<5] <= T[b>5]\";");
		L.add("eval test506 \"TH[a+c] + TH[b-d] = 0\";");
		L.add("eval test507 \"TH[a+c] - TH[b-d] = 0\";");
		L.add("eval test508 \"TH[a+c] * TH[b-d] = 4\";");
		L.add("eval test509 \"?msd_neg_2 TH[a+c] / TEST[b-d] = _2\";");
		L.add("eval test510 \"?msd_neg_2 TH[a+c] / TEST[b-d] = 2\";");
		L.add("eval test511 \"TH[a+c] = TH[b-d]\";");
		L.add("eval test512 \"T[a+c] <= T[b-d]\";");
		L.add("eval test513 \"TH[a<5] + TH[b-d] = 0\";");
		L.add("eval test514 \"TH[a<5] - TH[b-d] = 0\";");
		L.add("eval test515 \"TH[a<5] * TH[b-d] = 4\";");
		L.add("eval test516 \"?msd_neg_2 TH[a<5] / TEST[b-d] = _2\";");
		L.add("eval test517 \"?msd_neg_2 TH[a<5] / TEST[b-d] = 2\";");
		L.add("eval test518 \"TH[a<5] = TH[b-d]\";");
		L.add("eval test519 \"T[a<5] <= T[b-d]\";");

		// inf quantifier tests
		L.add("eval test520 \"?lsd_10 Ix x > 0\";");
		L.add("eval test521 \"?msd_10 Ix x + y = z & z <= 5\";");
		L.add("eval test522 \"?msd_neg_10 Ix 2*x = y & y >5\";");

		// more split/rsplit tests
		L.add("split test523 FTM[+]");
		L.add("split test524 FASQ[-]");
		L.add("rsplit test525[+] FASQ");
		L.add("rsplit test526[-] FTM");


		// transduce tests
		L.add("transduce test527 RUNSUM2 T;"); // msd_2 transduce
		L.add("transduce test528 RUNSUM3 MW;"); // msd_3 transduce
		L.add("transduce test529 RUNSUM2 PR;"); // lsd_2 transduce
		L.add("transduce test530 RUNSUM2 F;"); // msd_fib transduce
		
		L.add("reverse test531 F;"); // reverse F.
		L.add("transduce test532 RUNSUM2 test531;"); // lsd_fib transduce
		L.add("reverse test533 test532;");
		L.add("eval test534 \"?msd_fib An test533[n] = test530[n]\";");



		// check that reversal of reversal is the same as original
		L.add("reverse test535 test531;");
		L.add("eval test536 \"?msd_fib An test535[n] = F[n]\";");
		
		L.add("reverse test537 PR;");
		L.add("reverse test538 test537;");
		L.add("eval test539 \"?lsd_2 An test538[n] = PR[n]\";");



		// convert tests
		L.add("convert test540 msd_4 T;");
		L.add("convert test541 lsd_2 test540;");
		L.add("reverse test542 test541;");
		L.add("eval test543 \"An test542[n] = T[n]\";");

		L.add("convert test544 msd_2 HC;");
		L.add("convert test545 msd_32 test544;");
		L.add("convert test546 msd_32 HC;");
		L.add("eval test547 \"?msd_32 An test545[n] = test546[n]\";");

		// test incorrect base errors for convert.
		L.add("convert test548 msd_5 T;");
		L.add("convert test549 lsd_9 HC;");

		// test transduce incorrect output error
		L.add("transduce test550 RUNSUMmod2 TH;");
		L.add("transduce test551 RUNSUMmod2 TR;");

		// test transduce multiple inputs error.
		L.add("transduce test552 RUNSUMmod3 PF;");
		L.add("transduce test553 RUNSUMmod2 HS;");

		// test not k automatic convert error.
		L.add("convert test554 msd_2 FTM;");

		// test that the number systems are different
		L.add("convert test555 msd_2 T;"); 

		// test multiple input converts.
		L.add("convert test556 msd_4 PF;");

		// test negative numbers in regex
		L.add("reg test557 {-1,0,1} \"(11|[-1][-1])\";");
		L.add("reg test558 {-1,0,1} \"([-1][-1]|11)\";");
		L.add("eval test559 \"An $test557(n) <=> $test558(n) \";");
	}
	public void runPerformanceTest(String name,int numberOfRuns) throws Exception{
		PrintWriter out = new PrintWriter(new FileOutputStream(new File(directoryAddress+performanceTestFileName), true /* append = true */));
		out.println("----------------------------------------");
		out.println("Performance Test Result for " + name);
		out.println("Number of runs: " + numberOfRuns);
		out.println("Number of testcases: " + L.size());
		long total = 0;
		for(int i=0;i!=numberOfRuns;++i){
			long runtime = runTestCases();
			out.println((i+1) + "th run: " + runtime + "ms");
			total += runtime;
		}
		out.println();
		out.println("total: " + total + "ms");
		out.println("run average: " + total/numberOfRuns + "ms");
		out.println("testcase average: " + total/(numberOfRuns*L.size()) + "ms");
		out.println("----------------------------------------");
		out.close();
	}
	public long runTestCases() throws Exception{
		return runTestCases(0,L.size());
	}
	public long runTestCases(int begin) throws Exception{
		return runTestCases(begin,L.size());
	}
	public long runTestCases(int begin, int end) throws Exception{
		loadTestCases();
		int failedTestsCount = 0;
		int mplFailedTestsCount = 0;
		int detailsFailedTestsCount = 0;
		int errorFailedTestsCount = 0;
		int automataFailedTestsCount = 0;
		long before = 0;
		long after = 0;
		long total = 0;
		if(testCases == null || testCases.size() == 0)return total;
		System.out.println("Running test cases from test case " + begin +" to test case " + end);
		for(int i = begin; i < end;i++){
			TestCase expected = testCases.get(i);
			String command = L.get(i);
			System.out.println("\t\t"+command);
			try{
				before = System.currentTimeMillis();
				TestCase actual = Prover.dispatchForIntegrationTest(command);
				after = System.currentTimeMillis();
				total += (after-before);

				if(!conformMPL(expected.mpl.trim(),actual.mpl.trim())){
					failedTestsCount++;
					mplFailedTestsCount++;
					System.out.println("Test " + i + " failed! Actual and expected .mpl files do not conform.\n");
					continue;
				}

				if(!conformDetails(expected.details.trim(),actual.details.trim())){
					failedTestsCount++;
					detailsFailedTestsCount++;
					System.out.println("Test " + i + " failed! Actual and expected detailed logs do not conform.\n");
					continue;
				}

				if((actual.result == null && expected.result != null) ||
						(actual.result != null && expected.result == null) ||
						!actual.result.equals(expected.result)){
					failedTestsCount++;
					automataFailedTestsCount++;
					System.out.println("Test " + i + " failed! Actual and expected automata do not conform.\n");
				}
			}
			catch(Exception e){
				if(!e.getMessage().equals(expected.error)){
					errorFailedTestsCount++;
					failedTestsCount++;
					System.out.flush();
					System.out.println("Test " + i + " failed! Actual and expected error messages do not conform.\n");
					System.out.println("Expected error: " + expected.error);
					System.out.println("Actual error: " + e.getMessage());
				}
			}
		}
		if(failedTestsCount == 0){
			System.out.println("All tests passed!\n");
		}
		else{
			System.out.println(failedTestsCount + " test cases failed!");
			System.out.println(automataFailedTestsCount + " test cases failed because of resulting automata mistmach!");
			System.out.println(errorFailedTestsCount + " test cases failed because of error messages mistmach!");
			System.out.println(mplFailedTestsCount + " test cases failed because of mpl mistmach!");
			System.out.println(detailsFailedTestsCount + " test cases failed because of detailed logs mistmach!");
		}
		return total;
	}

	private boolean conformMPL(String expected_mpl,String actual_mpl){
		if(expected_mpl == null && actual_mpl == null)return true;
		if(expected_mpl.length() == 0 && actual_mpl.length() == 0) return true;
		//if(expected_mpl.length() != actual_mpl.length()){
		//	return false;
		//}
		if(expected_mpl.equals(actual_mpl)) return true;
		return false;
	}

	private boolean conformDetails(String expected_details,String actual_details){
		if(expected_details == null && actual_details == null)return true;
		if(expected_details.length() == 0 && actual_details.length() == 0) return true;
		expected_details = expected_details.replaceAll("\\d+ms", "");
		actual_details = actual_details.replaceAll("\\d+ms", "");
		return expected_details.equals(actual_details);
		/*String regex = "(.*)\\s*";
		String time = "(.*)(\\d+ms)$";
		Pattern pattern = Pattern.compile(regex);
		Matcher expected_matcher = pattern.matcher(expected_details);
		Matcher actual_matcher = pattern.matcher(actual_details);
		Pattern timePattern = Pattern.compile(time);
		while(expected_matcher.find()){
			System.out.println("expected:"+ expected_matcher.group(0)+")");
			if(!actual_matcher.find()){
				return false;
			}
			String expected = expected_matcher.group(0);
			String actual = actual_matcher.group(0);
			Matcher expected_time = timePattern.matcher(expected);
			Matcher actual_time = timePattern.matcher(actual);
			if(expected_time.find()){
				expected = expected_time.group(0);
			}
			if(actual_time.find()){
				actual = actual_time.group(0);
			}

			System.out.println("actual:"+ actual+")");

			if(actual.compareTo(expected) != 0){
				return false;
			}
		}
		if(actual_matcher.find()){
			return false;
		}
		return true;*/
	}

	public void loadTestCases() throws Exception{
		String command;
		testCases = new ArrayList<TestCase>();
		for(int i = 0 ; i < L.size();i++){
			command = L.get(i);
			Automaton M = null;
			StringBuffer error = new StringBuffer();
			StringBuffer details = new StringBuffer();
			StringBuffer mpl = new StringBuffer();
			if(new File(directoryAddress+"automaton"+Integer.toString(i)+".txt").isFile()){
				M = new Automaton(directoryAddress+"automaton"+i+".txt");
			}
			if(new File(directoryAddress+"error"+Integer.toString(i)+".txt").isFile()){
				BufferedReader errorReader = new BufferedReader(new InputStreamReader(new FileInputStream(directoryAddress+"error" + Integer.toString(i)+".txt"), "utf-8"));
				String temp;
				boolean flag = false;
				while((temp = errorReader.readLine())!= null){
					if(flag)
						error.append(UtilityMethods.newLine() + temp);
					else
						error.append(temp);
					flag = true;
				}
				errorReader.close();
			}

			if(new File(directoryAddress+"mpl"+Integer.toString(i)+".mpl").isFile()){
				BufferedReader mplReader = new BufferedReader(new InputStreamReader(new FileInputStream(directoryAddress+"mpl" + Integer.toString(i)+".mpl"), "utf-8"));
				String temp;
				boolean flag = false;
				while((temp = mplReader.readLine())!= null){
					if(flag)
						mpl.append(UtilityMethods.newLine() + temp);
					else
						mpl.append(temp);
					flag = true;
				}
				mplReader.close();
			}

			if(new File(directoryAddress+"details"+Integer.toString(i)+".txt").isFile()){
				BufferedReader detailsReader = new BufferedReader(new InputStreamReader(new FileInputStream(directoryAddress+"details" + Integer.toString(i)+".txt"), "utf-8"));
				String temp;
				boolean flag = false;
				while((temp = detailsReader.readLine())!= null){
					if(flag)
						details.append(UtilityMethods.newLine() + temp);
					else
						details.append(temp);
					flag = true;
				}
				detailsReader.close();
			}

			testCases.add(new TestCase(command,M,error.toString(),mpl.toString(),details.toString()));
		}
	}
	public void createTestCases() throws Exception{
		for(int i = 0; i < L.size();i++){
			String command = L.get(i);
			System.out.println(command);
			TestCase test_case = null;
			try{
				test_case = Prover.dispatchForIntegrationTest(command);
			}
			catch(Exception e){
				test_case = new TestCase(command,null,e.getMessage(),"","");
			}
			testCases.add(test_case);
		}
		writeTestCases();
	}
	private void writeTestCases() throws Exception{
		new File(directoryAddress).mkdirs();
		for(int i = 0 ; i < testCases.size();i++){
			TestCase t = testCases.get(i);
			if(t.result != null){
				t.result.write(directoryAddress+"automaton" +Integer.toString(i)+ ".txt");
			}
			if(t.error != null && t.error.length() > 0){
				PrintWriter errorWriter = new PrintWriter(directoryAddress+"error"+Integer.toString(i)+".txt", "UTF-8");
				errorWriter.println(t.error);
				errorWriter.close();
			}
			if(t.mpl != null && t.mpl.length() > 0){
				PrintWriter mplWriter = new PrintWriter(directoryAddress+"mpl"+Integer.toString(i)+".mpl", "UTF-8");
				mplWriter.println(t.mpl);
				mplWriter.close();
			}
			if(t.details != null && t.details.length() > 0){
				PrintWriter detailsWriter = new PrintWriter(directoryAddress+"details"+Integer.toString(i)+".txt", "utf-8");
				detailsWriter.println(t.details);
				detailsWriter.close();
			}
		}
	}
}
