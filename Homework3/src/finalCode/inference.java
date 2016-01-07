package finalCode;


import java.util.*;
import java.util.regex.Pattern;
import java.io.*;

public class inference {

	public static void main(String[] args) throws IOException {
		
//	    long startTime = System.currentTimeMillis();
//
//	    File inFile = null;
//		if (0 < args.length) {
//		   inFile = new File(args[1]);
//		} else {
//		   System.err.println("Invalid arguments count:" + args.length);
//		   System.exit(0);
//		}
		
		File dir = new File("/Users/Anushila/Dropbox/Fall 2015/AI/Homeworks/Homework 3");
		File fin = new File(dir.getCanonicalPath() + File.separator + "input_1.txt");
		 
//		readFile(inFile);
		
		readFile(fin);
		
//		long endTime   = System.currentTimeMillis();
//		long totalTime = endTime - startTime;
//		System.out.println(totalTime);


	}

	private static void readFile(File fin) throws IOException {
		
		BufferedReader br = new BufferedReader(new FileReader(fin));
		
		//Reading Number of Test cases
		String firstLine=br.readLine().trim();
		int totalQueries=Integer.parseInt(firstLine);
		LogicInference l = new LogicInference();
		
		//Reading Task Data
		for(int i=0;i<totalQueries;i++){
			
			String query=br.readLine().trim();
			QueryClass q = new QueryClass(query);
			l.addQuery(q);
			
		}
		
		int kBlength = Integer.parseInt(br.readLine().trim());
		
		for(int i=0; i<kBlength; i++){
			
			String rule = br.readLine();
			
			if(l.isAtomic(rule)){
				if(!l.facts.containsKey(rule.split(Pattern.quote("("))[0])){
					ArrayList<String> al = new ArrayList<String>();
					al.add(rule);
					l.facts.put(rule.split(Pattern.quote("("))[0], al);
				}
				else{
					ArrayList<String> original=l.facts.get(rule.split(Pattern.quote("("))[0]);
					original.add(rule);
					l.facts.put(rule.split(Pattern.quote("("))[0], original);
				}
				
//				ArrayList<String> al = new ArrayList();
//				l.facts.put(rule.split(Pattern.quote("("))[0], al.add(rule));
				
			}
				
			else
				l.knowledgeBase.add(rule);

			
		}
		
//		System.out.println(l.knowledgeBase);
//		System.out.println(l.facts);
//		System.out.println(l.queriesToBeInferred);
//		System.out.println("Hey");
//		System.out.println(l.knowledgeBase.size());
//		System.out.println(l.facts.size());
//		System.out.println(l.queriesToBeInferred.size());


//		l.mainInference();
//		
//		
		for(int i=0;i<l.queriesToBeInferred.size();i++){
			l.mainInference(l.queriesToBeInferred.get(i));
//			System.out.println(l.queriesToBeInferred.get(i).queryCanBeInferred);
		}
		
		l.printFunc();
			

		
	}

}
