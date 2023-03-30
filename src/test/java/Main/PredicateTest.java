package Main;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.nio.file.DirectoryNotEmptyException;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import Token.Token;

public class PredicateTest {
	static class Test {
		public Test(int i,String macro_,String pred_,String expected_predicate_,String expected_){
			this.macro = macro_;
			this.pred = pred_;
			this.expected_predicate = expected_predicate_;
			this.expected = expected_;
		}
		public String macro,pred,expected,expected_predicate;
		public int i;
	}
	public static void main(String[] args) {
		List<Test> tests = new ArrayList<Test>();
		tests.add(new Test(
				0,
				"%0",
				"#my_macro(a)=1",
				"a=1",
				"a 1 =_msd_2"));
		tests.add(new Test(
				1,
				"%0",
				"#my_macro(a) =1",
				"a =1",
				"a 1 =_msd_2"));
		tests.add(new Test(
				2,
				"%0",
				" #my_macro(a) =1",
				" a =1",
				"a 1 =_msd_2"));
		tests.add(new Test(
				3,
				"%0=1",
				"?msd_3 (#my_macro(a))",
				"?msd_3 (a=1)",
				"a 1 =_msd_3"));
		tests.add(new Test(
				4,
				"%0=1",
				"?msd_3 ( #my_macro(a))",
				"?msd_3 ( a=1)",
				"a 1 =_msd_3"));
		tests.add(new Test(
				5,
				"%0=1",
				"?msd_3 (#my_macro(a) )",
				"?msd_3 (a=1 )",
				"a 1 =_msd_3"));
		tests.add(new Test(
				6,
				"%0=1",
				"?msd_3 (#my_macro(a) => #my_macro(b))",
				"?msd_3 (a=1 => b=1)",
				"a 1 =_msd_3 b 1 =_msd_3 =>"));
		tests.add(new Test(
				7,
				"a+b=2",
				"#my_macro()",
				"a+b=2",
				"a b +_msd_2 2 =_msd_2"));
		tests.add(new Test(
				8,
				"a+b=2",
				"#my_macro() & #my_macro()",
				"a+b=2 & a+b=2",
				"a b +_msd_2 2 =_msd_2 a b +_msd_2 2 =_msd_2 &"));
		tests.add(new Test(
					9,
					"%0 E%1 %2 = %1 + 1 & %1 = 5",
					"#my_macro(?msd_2,a,b)",
					"?msd_2 Ea b = a + 1 & a = 5",
					"a b a 1 +_msd_2 =_msd_2 a 5 =_msd_2 & E"));
		tests.add(new Test(
				10,
				"%0 E%1 %2 = %1 + 1 & %1 = 5",
				"#my_macro(?msd_3,a,b)",
				"?msd_3 Ea b = a + 1 & a = 5",
				"a b a 1 +_msd_3 =_msd_3 a 5 =_msd_3 & E"));
		tests.add(new Test(
				11,
				"%0 E%1 %2 = %1 + 1 &",
				"#my_macro(?msd_2,a,b) a = 5",
				"?msd_2 Ea b = a + 1 & a = 5",
				"a b a 1 +_msd_2 =_msd_2 a 5 =_msd_2 & E"));
		tests.add(new Test(
				12,
				"E%0 %1 = %0 + 1 &",
				"?msd_fib #my_macro(a,b) a = 5",
				"?msd_fib Ea b = a + 1 & a = 5",
				"a b a 1 +_msd_fib =_msd_fib a 5 =_msd_fib & E"));
		tests.add(new Test(
				13,
				"E%0 %1 = %0 + 1 &",
				"?msd_fib (#my_macro(a,b) a = 5) =>(?lsd_3   #my_macro(f,g) f = 6)",
				"?msd_fib (Ea b = a + 1 & a = 5) =>(?lsd_3   Ef g = f + 1 & f = 6)",
				"a b a 1 +_msd_fib =_msd_fib a 5 =_msd_fib & E f g f 1 +_lsd_3 =_lsd_3 f 6 =_lsd_3 & E =>"));
		for(int i=0;i!=tests.size();++i){
			Test t = tests.get(i);
			t.i = i;
			test(t);
		}
	}
	
	private static void create_macro(String name, String macro){
		try{
			BufferedWriter out = 
					new BufferedWriter(
							new OutputStreamWriter(
									new FileOutputStream(
											UtilityMethods.get_address_for_macro_library()+name+".txt"), "utf-8"));
			out.write(macro);
			out.close();
		}
		catch (Exception o){
			o.printStackTrace();
//			throw new Exception("Could not create macro: " + name);
		}
	}
	private static void delete_macro(String name){
		try {
		    Files.delete(Paths.get(UtilityMethods.get_address_for_macro_library()+name+".txt"));
		} catch (NoSuchFileException x) {
		    System.err.format("%s: no such" + " file or directory%n");
		} catch (DirectoryNotEmptyException x) {
		    System.err.format("%s not empty%n");
		} catch (IOException x) {
		    // File permission problems are caught here.
		    System.err.println(x);
		}
	}
	private static String post_to_string(List<Token> p){
		String s = "";
		for(Token t:p){
			s += t.toString() + " ";
		}
		return s;
	}
	private static void test(Test t){
		int i = t.i;
		String macro = t.macro;
		String pred = t.pred;
		String expected = t.expected;
		String expected_predicate = t.expected_predicate;
		
		//System.out.println(macro);
		//System.out.println(pred);
		create_macro("my_macro",macro);
		try {
			Predicate p = new Predicate(pred);
			//System.out.println(p.predicate);
			String s = post_to_string(p.postOrder);
			//System.out.println(s);
			if(p.predicate.trim().compareTo(expected_predicate.trim()) != 0){
				System.out.println("test " + i +" failed.\n predicate: "+ p.predicate.trim() +" \n Expected predicate: " + expected_predicate);
			}
			if(s.trim().compareTo(expected.trim())!=0){
				System.out.println("test " + i +" failed.\n Result: "+ s +" \n Expected: " + expected);
			}
		
		} catch (Exception e) {
			System.out.println("Exception thrown: test1 failed");
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
		delete_macro("my_macro");
		return;
	}
}
