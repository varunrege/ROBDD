//import java.util.*;
import java.lang.*;
import java.util.Scanner;


import com.udojava.evalex.*; //External parser
public class ROBDD{

    private int[][] T;
    private int[] H;
    private int nodeCount;   
    private int capacity;
    private int[][] G;
    private int[][] T1;
    private int[][] T2;
    private int T1NodeCount;
    private int T2NodeCount;
    private String op;
    private int variable;
    private int[][] TUR;
    private int TURNodeCount;
    private int restrictVar;
    private int restrictVal;
    private int[] R;
    private int[] SATCountTable;
    private int[] SATAssignment;
    private boolean SATISFIABLE;

    
    public ROBDD(int n){
        nodeCount = 0;
        capacity = n;
        variable = n;
        T = new int[capacity][3];
        
        //-1 indicates NULL.
        T[0][0] = n+1;
        T[0][1] = -1;
        T[0][2] = -1;
        T[1][0] = n+1;
        T[1][1] = -1;
        T[1][2] = -1;
        nodeCount += 2;
        
        H = new int[capacity];
        for(int i=0;i<capacity;i++)
            H[i] = -1; 
    }
    

    public int getNodeCount(){
        return nodeCount;
    }
    

    public int[][] getROBDDTable(){
        return T;
    }
    
    private boolean member(int i, int l, int h){
        int hashCode = generateHash(i,l,h);
        // Not present in extended capacity
        if(hashCode>(H.length-1)) return false;
        // Not present in current capacity
        return H[hashCode] != -1 ;
    }
     
    private int lookup(int i,int l,int h){
            int hashCode = generateHash(i,l,h);
            return H[hashCode];    
        }
 
    private void insert(int i,int l,int h,int node){
        int hashCode = generateHash(i,l,h);
        if(hashCode>(H.length+1)) renewHashTable(hashCode);
        if(H[hashCode] != -1) renewHashTable(hashCode);
        H[hashCode] = node;
        return;    
    }

    public int mk(int i,int l,int h){
        if(l == h)
        {
            return l;            
        }
        else if(member(i,l,h))
        {
            return lookup(i,l,h);
        }
        else
        { 
            int node = add(i,l,h);
            insert(i,l,h,node);
            return node;
        }
        
    }

    private boolean eval(String exp){
        Expression e = new Expression(exp);
        String result = String.valueOf(e.eval());
        int resultInt = Integer.parseInt(result);
        if(resultInt == 1) return true;
        else return false;
    }
    
    private String newExp(String exp,int var,int val){
        String varStr = "x" + String.valueOf(var);
        String valStr = String.valueOf(val);
        String newExpStr = exp.replaceAll(varStr,valStr);
        return newExpStr;
    }                
    
    public int build(String exp,int i){
        if(i > variable){
            if(eval(exp)) return 1;
            else return 0;
        }else{
            int l = build(newExp(exp,i,0),i + 1);
            int h = build(newExp(exp,i,1),i + 1);
            return mk(i,l,h);
        }
    }
    public void apply(String op,ROBDD u1, ROBDD u2){
        T1 = u1.getROBDDTable();
        T2 = u2.getROBDDTable();
        T1NodeCount = u1.getNodeCount();
        T2NodeCount = u2.getNodeCount();
        G = new int[T1NodeCount][T2NodeCount];
        this.op = op;
        for(int i=0;i<T1NodeCount;i++){
            for(int j=0;j<T2NodeCount;j++){
                G[i][j] = -1;
            }
        }
        
        app(T1NodeCount-1,T2NodeCount-1);        
    }
    
    private int app(int l,int h){
        int u;
        if(G[l][h] != -1){ 
            return G[l][h];
        }else if( ((l==0)||(l==1)) && ((h==0)||(h==1)) ) {
            u = eval(String.valueOf(l) + op + String.valueOf(h))?1:0;
        }else if(T1[l][0] == T2[h][0]){
            u = mk(T1[l][0], app(T1[l][1],T2[h][1]) , app(T1[l][2],T2[h][2]));
        }else if(T1[l][0] < T2[h][0]){
            u = mk(T1[l][0], app(T1[l][1],h), app(T1[l][2],h) );
        }else{
            u = mk(T1[h][0], app(l,T2[h][1]), app(l,T2[h][2]) );
        }
        G[l][h] = u;
        return u;
    }
    
    public void restrict(ROBDD u,int var,int val){
        TUR = u.getROBDDTable();
        TURNodeCount = u.getNodeCount();
        restrictVar = var;
        restrictVal = val;
        R = new int[TURNodeCount];
        for(int i=0;i<TURNodeCount;i++)
        R[i] = -1;
        res(TURNodeCount-1);
        
    }
    
    private int res(int node){
        if(alreadyRestricted(node)) return node; 
        if(TUR[node][0]>restrictVar){
            buildROBDD(node); 
            R[node] = 1;
            return node;   
        }else if(TUR[node][0]<restrictVar){
            R[node] = 1;
            return mk(TUR[node][0],res(TUR[node][1]),res(TUR[node][2]));
        }else{
            if(restrictVal == 0){
                R[node] = 1;
                return res(TUR[node][1]);
            }else{
                R[node] = 1;
                return res(TUR[node][2]);
            }
        }
    }
    private void buildROBDD(int root){
        if(root == 0 || root == 1) return; 
        int i = TUR[root][0];
        int l = TUR[root][1];
        int h = TUR[root][2];
        buildROBDD(l);
        buildROBDD(h);
        mk(i,l,h);
    }
    
    private boolean alreadyRestricted(int node){
        return R[node] != -1;
    }
    
    public int SATCount(ROBDD u){
        T = u.getROBDDTable();
        nodeCount = u.getNodeCount();
        SATCountTable = new int[nodeCount];
        for(int i=0;i<nodeCount;i++) SATCountTable[i] = -1;
        int solutions = count(nodeCount - 1);
        return solutions;
    }    
    
    public int[] ANYSAT(ROBDD u){
        SATISFIABLE = true;
        T = u.getROBDDTable();
        nodeCount = u.getNodeCount();
        SATAssignment = new int[variable];
        for(int i=0;i<variable;i++) SATAssignment[i] = -1;
        genANYSAT(nodeCount - 1);
        if(SATISFIABLE)
        assignArbit();
        return SATAssignment;
    }
    
    private void genANYSAT(int node){
        
        if(node == 0 ){
            SATISFIABLE = false;
            return;
        }
        
        if(node == 1) return;
        else{
            if(T[node][1] == 0){
                SATAssignment[T[node][0]-1] = 1;
                genANYSAT(T[node][2]);
                return;    
            }else{
                SATAssignment[T[node][0]-1] = 0;
                genANYSAT(T[node][1]);
                return;
            }    
        }
    }
    
    private void assignArbit(){
        for(int i=0;i<variable;i++)
        if(SATAssignment[i] == -1) SATAssignment[i] = 1;
        return;    
    }
    
    private int count(int node){
        if(SATVisited(node)) return SATCountTable[node];
        if(node == 0 || node == 1) return node;
        else{
            int arbitAssignLow = (int) Math.pow(2,T[T[node][1]][0]-T[node][0]-1);
            int totalAssignLow = arbitAssignLow*count(T[node][1]);
            int arbitAssignHigh = (int) Math.pow(2,T[T[node][2]][0]-T[node][0]-1);
            int totalAssignHigh = arbitAssignHigh*count(T[node][2]);
            return totalAssignHigh + totalAssignLow;
        }
    }
    
    private boolean SATVisited(int node){
        return SATCountTable[node] != -1;
    }

    private int add(int i,int l,int h){
        int curNodeIndex = nodeCount++;
        if(curNodeIndex == capacity) expandArray();
        T[curNodeIndex][0] = i;
        T[curNodeIndex][1] = l;
        T[curNodeIndex][2] = h;
        return curNodeIndex;
    }
    
    
    private void expandArray(){
        capacity *= 2;
        int[][] temp = new int[capacity][3];
        for(int i=0;i<T.length;i++){
            temp[i][0] = T[i][0];
            temp[i][1] = T[i][1];
            temp[i][2] = T[i][2];
        }
        T = temp;
    }
    
    private int generateHash(int i,int l,int h){
        int hashCode = (pair(i,pair(l,h)));
        return hashCode;    
    }   
    
    private int pair(int i,int j){
        return (((i+j)*(i+j+1))/2 + i);
    } 
    
    private void renewHashTable(int hashCode){
        int newSize = hashCode + 1;
        int[] newH= new int[newSize];
        for(int j=0;j<newSize;j++){
            newH[j] = -1;
        }
        for(int j=2;j<nodeCount;j++){
            int i = T[j][0];
            int l = T[j][1];
            int h = T[j][2];
            int hashCodeCur = generateHash(i,l,h);
            newH[hashCodeCur] = j; 
        }
        H = newH;
        return;
    }
    
    public void print(){
        System.out.println("Table T\nu var low high");    
        for(int i=0;i<nodeCount;i++)
        {
            System.out.println(i + " " + T[i][0] 
            + " " + T[i][1] 
            + " " + T[i][2]);                      
        }
    }   
    
    public static void main(String[] args){
        int x;
        Scanner in = new Scanner(System.in);

        long start_time = System.currentTimeMillis();
        
        System.out.println("Electronic Design Automation\nLab 1: ROBDDs");
        System.out.println("Select operation: \n1. Build\n2. Apply\n3. Restrict\n4. SatCount and AnySat");
        x = in.nextInt();
        
        if (x < 1 || x > 4)
        {
            System.out.println("Invalid input");
        }
        switch(x)
        {
            case 1:
            ROBDD buildtest = new ROBDD(4);
            //String expr = "((x1) EQUIV (x2)) OR (x3)";
            //String expr = "(NOT (x1)) AND (x2 EQUIV (NOT (x3)))";
            //String expr = "((x1 AND x2) OR (NOT(x1 OR x2))) AND ((x3 AND x4) OR (NOT(x3 OR x4)))";
            String expr = "(x1 AND x2 AND x3 AND x4) OR ((NOT(x1)) AND (NOT(x2)) AND x3 AND x4) OR (x1 AND x2 AND (NOT(x3)) AND x4) OR ((NOT(x1)) AND (NOT(x2)) AND (NOT(x3)) AND x4)";
            buildtest.build(expr,1);
            buildtest.print();   
            break;

            case 2:
            //2. Apply
            ROBDD u1 = new ROBDD(5);
            String u1boolExp = "NOT (x1 AND x3)";
            //String u1boolExp = "((x1) EQUIV (x2)) AND ((x3) EQUIV (x4))";
            //String u1boolExp = "((x1 AND x2) OR (NOT(x1 OR x2))) AND ((x3 AND x4) OR (NOT(x3 OR x4)))";
            u1.build(u1boolExp,1);
            // u1.mk(5,1,0);
            // u1.mk(4,2,0);
            // u1.mk(4,0,2);
            // u1.mk(3,3,4);
            // u1.mk(2,5,0);
            // u1.mk(2,0,5);
            // u1.mk(1,6,7);
            // u1.print();
            ROBDD u2 = new ROBDD(5);
            String u2boolExp = "x2 AND x3";
            //String u2boolExp = "((x1) IMPL (x2)) AND ((x3) IMPL (x4))";
            //String u2boolExp = "(x1 AND x2 AND x3 AND x4) OR ((NOT(x1)) AND (NOT(x2)) AND x3 AND x4) OR (x1 AND x2 AND (NOT(x3)) AND x4) OR ((NOT(x1)) AND (NOT(x2)) AND (NOT(x3)) AND x4)";
            u2.build(u2boolExp,1);
            // u2.mk(5,1,0);
            // u2.mk(3,2,0);
            // u2.mk(3,0,2);
            // u2.mk(1,3,4);
            // u2.print();
            
            ROBDD result = new ROBDD(5);
            result.apply("||",u1,u2);
            result.print();
            //End Apply
            break;

            case 3:
            //3. Restrict
            ROBDD rtest = new ROBDD(4);
            //String rboolExp = "NOT(x1&&NOT(x2) || NOT(x1)&&x2)" + 
            //                 "&& NOT(x3&&NOT(x4) || NOT(x3)&&x4)";
            // String rboolExp = "(x1 EQUIV x2) && (x3 EQUIV x4)";
            //String rboolExp = "(x1 IMPL (x2 EQUIV x3)) && x4";
            
            //String rboolExp = "((x1) EQUIV (x2)) OR (x3)";
            //String rboolExp = "(NOT (x1)) AND (x2 EQUIV (NOT (x3)))";
            //String rboolExp = "((x1 AND x2) OR (NOT(x1 OR x2))) AND ((x3 AND x4) OR (NOT(x3 OR x4)))";
            String rboolExp = "(x1 AND x2 AND x3 AND x4) OR ((NOT(x1)) AND (NOT(x2)) AND x3 AND x4) OR (x1 AND x2 AND (NOT(x3)) AND x4) OR ((NOT(x1)) AND (NOT(x2)) AND (NOT(x3)) AND x4)";
            rtest.build(rboolExp,1);
            ROBDD rest = new ROBDD(4);
            rest.restrict(rtest,2,0);
            
            rtest.print();   
            rest.print();
            //End Restrict
            break;

            case 4:
            //4. SatCount, AnySat
            ROBDD stest = new ROBDD(4);
            //String sboolExp = "NOT(x1&&NOT(x2) || NOT(x1)&&x2)" + 
            //                 "&& NOT(x3&&NOT(x4) || NOT(x3)&&x4)";
            //String sboolExp = "(NOT(x1) OR (x2)) AND (NOT(x3) OR (x4))";
            
            //String sboolExp = "((x1) EQUIV (x2)) OR (x3)";
            //String sboolExp = "(NOT (x1)) AND (x2 EQUIV (NOT (x3)))";
            //String sboolExp = "((x1 AND x2) OR (NOT(x1 OR x2))) AND ((x3 AND x4) OR (NOT(x3 OR x4)))";
            String sboolExp = "(x1 AND x2 AND x3 AND x4) OR ((NOT(x1)) AND (NOT(x2)) AND x3 AND x4) OR (x1 AND x2 AND (NOT(x3)) AND x4) OR ((NOT(x1)) AND (NOT(x2)) AND (NOT(x3)) AND x4)";
            
            // String sboolExp = "(x1 EQUIV x2) && (x3 EQUIV x4)";
            // String sboolExp = "(x1 IMPL (x2 EQUIV x3)) && x4";
            
            stest.build(sboolExp,1);
            
            ROBDD testSat= new ROBDD(4);
            int assgns = testSat.SATCount(stest);
            int[] SATassgn = testSat.ANYSAT(stest);
            System.out.println("SatCount: " + assgns);
            String sat = "";
            for(int i=0;i<SATassgn.length;i++)
                sat += " " + String.valueOf(SATassgn[i]);
            System.out.println("Any One Sat:"+ sat);    
            stest.print();
            break;
        }

        long total_time = System.currentTimeMillis() - start_time;

        System.out.println("Total Time is: "+total_time);
    }   
}
