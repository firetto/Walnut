package Automata;

import java.util.ArrayList;

public class Partition {
	static int[] M,W;
	static int w = 0;
	
	int z;
	Integer[] E;
	int []L,S,F,P;

	void init( int n ){
	    z = n == 0? 0:1;  
	    E = new Integer[n];
	    L = new int[n]; S = new int[n];
	    F = new int[n]; P = new int[n];
	    for( int i = 0; i < n; ++i ){
	      E[i] = L[i] = i; S[i] = 0; 
	      F[i] = P[i] = 0;
	    }
	    if( z != 0 ){ F[0] = 0; P[0] = n; }
	}

	void mark( int e ){
		int s = S[e];
		int i = L[e];
		int j = F[s]+M[s];
		/*System.out.println("s = " + s);	
		System.out.println("F[s] = " + F[s]);	
		System.out.println("M[s] = " + M[s]);
		System.out.println("i = " + i);
		System.out.println("j = " + j);
		System.out.println("|E| = " + E.length);*/

	    E[i] = E[j]; 
	    L[E[i]] = i;
	    E[j] = e; L[e] = j;
	    if( M[s]++ == 0 ){ W[w++] = s; }
	}

	void split(){
		while( w > 0 ){
			int s = W[--w], j = F[s]+M[s];
		    if( j == P[s] ){M[s] = 0; continue;}
		    if( M[s] <= (P[s]-j) ){
		    	F[z] = F[s]; P[z] = F[s] = j; 
		    }
		    else{
		        P[z] = P[s]; F[z] = P[s] = j; 
		    }
		    for( int i = F[z]; i < P[z]; ++i ){
		    	S[E[i]] = z; 
		    }
		    M[s] = M[z++] = 0;
		}
	}
}
