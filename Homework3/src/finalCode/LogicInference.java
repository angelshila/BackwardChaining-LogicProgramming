package finalCode;


import java.io.*;
import java.util.*;
import java.util.regex.Pattern;


public class LogicInference {

	private String COMMA = ",";
	private ArrayList < String > visitedRules = new ArrayList < String > ();
	private ArrayList < Boolean > output = new ArrayList < Boolean > ();
	public ArrayList < QueryClass > queriesToBeInferred = new ArrayList < QueryClass > ();
	public ArrayList < String > knowledgeBase = new ArrayList < String > ();
	public HashMap < String, ArrayList < String >> facts = new HashMap < String, ArrayList < String >> ();
	private String IMPLIES = "=>";
	private String AND = "\\^";
	private String PREDICATE_SEPARATOR = Pattern.quote("(");
	private String ARGS_SEPARATOR = Pattern.quote(",");
	
	

	//Add Queries
		public void addQuery(QueryClass query) {

			queriesToBeInferred.add(query);
		}
		
	//Check if rule is a fact
	public boolean isAtomic(String q) {
		
		return !q.contains(IMPLIES);
		
	}

	
	public void mainInference(QueryClass query) {

//		System.out.println(query.querySentence);
		
		//Sending empty HashMap
		HashMap < String, String > hm = new HashMap < String, String > ();
		ArrayList < HashMap < String, String >> result = backwardChaining(query.querySentence, hm);

		if (result != null) {
			query.queryCanBeInferred = true;
		}
		
		//Adding to output
		output.add(query.queryCanBeInferred);
		
		clearFunc();
		

		


	}

	private void clearFunc() {
		
		visitedRules.clear();
		
	}

	@SuppressWarnings({ "unused", "unchecked", "rawtypes" })
	private ArrayList < HashMap < String, String >> backwardChaining(String querySentence, HashMap < String, String > hm) {

		//Implementation for Clauses with empty hashmaps!
		boolean emptyHM = false;
		boolean notInHM = true;
		boolean allVars = true;
		boolean AnySub = false;


		if (hm.isEmpty()) emptyHM = true;

		ArrayList < HashMap < String, String >> tempListOfHM = new ArrayList<HashMap<String, String>>();
		String queryArgs[] = getArgs(querySentence);


		for (int i = 0; i < queryArgs.length; i++) {
			
			if (Character.isUpperCase(queryArgs[i].charAt(0))) {
				allVars = false;
				break;
			}
		}

		
		for (int i = 0; i < queryArgs.length; i++) {
			
			for (Map.Entry < String, String > entry: hm.entrySet()) {
				if (hm.containsKey(queryArgs[i])) {
					notInHM = false;
					break;
				}
			}

			if (!notInHM){ 
				break;
			}
		}


		//Visit a rule and keep track of this
		String currentQ = buildString(hm,querySentence.trim());

		//Keeping track of visited rules by storing in global arraylist.
		if (visitedRules.isEmpty()) {

			visitedRules.add(currentQ);
		} else {

			if (visitedRules.contains(currentQ)){ 
				
				return null;
			
			}
			else {
				if (!hm.isEmpty()) visitedRules.add(currentQ);
			}
		}

		//Parent(a,b) type cases		
		if ((emptyHM == true && allVars == true) 
				|| (notInHM == true && allVars == true)) {

			AnySub = true;

		}

		
		
		//1st check if you can unify this query with facts
		querySentence = querySentence.trim();
		ArrayList < HashMap < String, String >> checkUnify = canUnifyWithFacts(AnySub, querySentence, hm);

		if (checkUnify != null) {
			
			return checkUnify;
			
		} else {

		//if not, gather all those rules with which this query can be matched with. This forms the or part.
			Queue < String > orOfRules = new LinkedList < String > ();
			for (int i = 0; i < knowledgeBase.size(); i++) {
				if (canUnifyRules(getConsequent(knowledgeBase.get(i)), querySentence, hm)) {
					orOfRules.add(knowledgeBase.get(i));
				}

			}

			if (orOfRules.isEmpty()) {
				
				return null;
				
			} else {

				ArrayList < HashMap < String, String >> subs = new ArrayList<HashMap<String, String>>();
		// ArrayList<HashMap<String,String>> completeSubs = new ArrayList();

				//Processing each Rule
				while (!orOfRules.isEmpty()) {
					
					boolean failFlag = false;
					boolean failForOneRule = false;
					String rule = orOfRules.remove();
//					System.out.println(rule);
					String right = getConsequent(rule);
//					System.out.println(right);
					
					String conRule = getConsequent(rule).toString();
					
					HashMap < String, String > newMap = HMmerge(currentQ, right);
					
					//Get all the antecedents of a particular rule.
					String antecedents[] = getPremises(rule);

		//each clause must be true for the entire rule to be true. If one becomes wrong. break and try next rule i.e. or part

					int i = 0;
					while (i < antecedents.length && !failFlag) {


						//Get all possible substitutions
						subs = backwardChaining(antecedents[i], newMap);

						if (subs != null && i == antecedents.length - 1) {
							HashMap<String, String> newMapClone = (HashMap) hm.clone();
							tempListOfHM = superSetHashMaps(subs, newMapClone, querySentence, right, conRule);
							subs = tempListOfHM;
						}
						//						
						i++;
						
						if (subs != null && !failFlag) {

							int totalNoSubs = subs.size();

							for (int k = 0; k < subs.size() && i < antecedents.length; ++k) {
								failFlag = false;
								//								ArrayList <HashMap<String,String>> completelistOfHM= new ArrayList();
								ArrayList < HashMap < String, String >> listOfHM = backwardChaining(antecedents[i], subs.get(k));

								if (listOfHM != null) {
									subs = listOfHM;
								}

								if (listOfHM != null && i == antecedents.length - 1) {

									HashMap<String, String> newMapClone = (HashMap) hm.clone();
									tempListOfHM = superSetHashMaps(subs, newMapClone, querySentence, right, conRule);

									subs = tempListOfHM;

								}


								if (listOfHM != null) {
									i++;
									if (k < subs.size()) {
										newMap = listOfHM.get(k);
									}
								}


								if (listOfHM != null && i >= antecedents.length) {
									return tempListOfHM;
								}

								if (listOfHM == null) {
									failFlag = true;
								}
								if (failFlag == true && k < subs.size()) {
									//									failFlag=false;
									continue;
								}



							}
						} else {
							failForOneRule = true;
							break;
						}
					}
					if (failFlag) {
						//						failFlag=false;
						return null;
					}

					if (failForOneRule) {
						//						failForOneRule=false;
						continue;
					}
					if (!tempListOfHM.isEmpty()) {
						break;
					}

				}
				return subs;
			}


		}

	}

	

	@SuppressWarnings({ "unused", "unchecked", "rawtypes" })
	private ArrayList <HashMap<String,String>> canUnifyWithFacts(boolean substituteAnyVal, String q, HashMap<String, String> hm) {
		//Get the different substitutions

		String[] predicateQ = q.split(PREDICATE_SEPARATOR);
		String[] argsQ = getArgs(q);
		int unifyCount = 0;
		ArrayList < HashMap < String, String >> substitutions = new ArrayList < > ();

		if (substituteAnyVal) {

			ArrayList < HashMap < String, String >> allHashMaps = new ArrayList();
			boolean similarNo = false;
			HashMap < String, String > mapNew = new HashMap();

			if (facts.containsKey(predicateQ[0].trim())) {
				ArrayList < String > factList = facts.get(predicateQ[0].trim());

				if (!factList.isEmpty()) {

					String factArguments[] = getArgs(factList.get(0));

					if (argsQ.length == factArguments.length) {

						for (int i = 0; i < argsQ.length; i++) {
							mapNew.put(argsQ[i], factArguments[i]);
						}

					}
				}
				allHashMaps.add(mapNew);
			}

			if (!allHashMaps.isEmpty()) {

				return allHashMaps;
			}

		} else {


			if (facts.containsKey(predicateQ[0].trim())) {
				
				ArrayList < String > allFacts = facts.get(predicateQ[0].trim());
				boolean flagFound = false;

				for (int i = 0; i < allFacts.size(); i++) {
					if (q.equals(allFacts.get(i))) {
						flagFound = true;
						String[] argsR = getArgs(allFacts.get(i));
						HashMap<String,String> hmClone = (HashMap) hm.clone();
						for (int j = 0; j < argsR.length; j++) {
							hmClone.put(argsQ[j], argsR[j]);
						}
						if (!substitutions.contains(hmClone)) 
							substitutions.add(hmClone);
						break;
					}
				}


				if (!flagFound) {
					for (int i = 0; i < allFacts.size(); i++) {

						boolean failFlag = false;
						boolean flag_UpperCase = true;
						String[] argsR = getArgs(allFacts.get(i));
						//System.out.println(q.trim());
						//System.out.println(allFacts.get(i));
						HashMap<String,String> hmClone = (HashMap) hm.clone();
						for (int j = 0; j < argsR.length; j++) {

							if (argsR[j].equals(argsQ[j])) {
								continue;
							}
							//arguments not matching. so check if mapping exists
							else if (!argsR[j].equals(argsQ[j])) {
								//Creating a mapping
								if (!hmClone.containsKey(argsQ[j])) {
									if (Character.isLowerCase(argsQ[j].charAt(0))) {
										flag_UpperCase = false;
										hmClone.put(argsQ[j], argsR[j]);
									}
								} else if (hmClone.containsKey(argsQ[j])) {
									if (hmClone.get(argsQ[j]).equals(argsR[j])) {
										flag_UpperCase = false;
										continue;
									} else {
										failFlag = true;
										break;
									}

								} else {
									failFlag = true;
									break;
								}

							}

						}
						
						if (!substitutions.contains(hmClone) && failFlag == false && !flag_UpperCase) substitutions.add(hmClone);
						//						ArrayList result=backwardChaining(newQuery,hmClone);

					}
				}

				if (!substitutions.isEmpty()){ 
					return substitutions;
				}

			}

		}

		return null;
	}


	@SuppressWarnings("unused")
	private boolean canUnifyRules(String rule, String q, HashMap<String, String> matchVars) {

		String[] predicateR = rule.split(PREDICATE_SEPARATOR);
		String[] predicateQ = q.split(PREDICATE_SEPARATOR);
		String[] argsR = getArgs(rule);
		String[] argsQ = getArgs(q);
		int unifyCount = 0;

		if (predicateR[0].trim().equals(predicateQ[0].trim()) && argsR.length == argsQ.length) {

			for (int i = 0; i < argsR.length; i++) {

				if (argsR[i].equals(argsQ[i])) unifyCount++;
				else if (matchVars.containsKey(argsR[i])) {
					if (matchVars.get(argsR[i]).equals(argsQ[i])) unifyCount++;
					//					else{
					//						matchVars.put(argsR[i], matchVars.get(argsQ[i]));
					//					}
				} else {
					if (!Character.isLowerCase(argsQ[i].charAt(0))) {
						matchVars.put(argsR[i], argsQ[i]);
					}

				}

			}

			//			Set<String> s1 = new HashSet();
			//			Set<String> s2 = new HashSet();
			//			for(int i =0;i<argsR.length;i++){
			//				s1.add(argsR[i]);
			//			}
			//			
			//			
			//			
			//			
			//			 Iterator it = matchVars.entrySet().iterator();
			//			    while (it.hasNext()) {
			//			        Map.Entry pair = (Map.Entry)it.next();
			//			        System.out.println(pair.getKey() + " = " + pair.getValue());
			//			        s2.add((String) pair.getKey());
			//			    }
			//			s2.removeAll(s1);
			//			
			//			
			//			for (String s : s2) {
			//			    System.out.println(s);
			//			    matchVars.remove(s);
			//			}


			return true;
		}

		return false;

	}

	public String[] getArgs(String q) {
		
		String[] splitArr = q.split(PREDICATE_SEPARATOR);
		
		String allArgs = splitArr[1];
		
		if (!allArgs.contains(",")) {
			
			
			String argument = allArgs.split(Pattern.quote(")"))[0];
			
			String[] argArr = new String[1];
			
			argArr[0] = argument;
			
			return argArr;
			
			
		} 
		
		
		else {
			
			String[] argsArr = allArgs.split(ARGS_SEPARATOR);
			
			String lastArg = argsArr[argsArr.length - 1].split(Pattern.quote(")"))[0];
			
			argsArr[argsArr.length - 1] = lastArg;
			
			return argsArr;
		}
	}


	private String buildString(HashMap < String, String > hm,String query) {

		//Get all the arguments to make up a new query
		String args[] = getArgs(query);
		int count = 0;
		for (int i = 0; i < args.length; i++) {
			
			if (!Character.isLowerCase(args[i].charAt(0))) {
				count++;
			}
		}

		if (count == args.length) {
			
			return query;
			
		} 
		else {
			
			String[] str = query.split(PREDICATE_SEPARATOR);
			String argsSubstituted[] = new String[args.length];

			for (int i = 0; i < args.length; i++) {
				
				if(!hm.containsKey(args[i].trim())) {
					argsSubstituted[i] = args[i];

				}
				
				
				else if (hm.containsKey(args[i].trim())) {
					argsSubstituted[i] = hm.get(args[i].trim());
				} 
				
			}

			
			String finalString="";
			finalString+=str[0];
			finalString+="(";
			
			for (int i = 0; i < argsSubstituted.length; i++) {
				finalString+=argsSubstituted[i];
				//reached end of arguments
				if (i == argsSubstituted.length - 1) {
					break;
				}
				finalString+=COMMA;
			}
			finalString+=")";

			return finalString;
		}

	}

	private String[] getPremises(String q) {
		
		String[] splitRule = q.split(IMPLIES);
		
		String[] premises = splitRule[0].split(AND);
		
		return premises;
	}

	@SuppressWarnings({ "unchecked", "rawtypes" })
	private ArrayList < HashMap < String, String >> superSetHashMaps(ArrayList < HashMap < String, String >> subs, HashMap < String, String > newMap, String query, String antecedent, String consequent) {

		String argsAntecedent[] = getArgs(query);
		String argsConsequent[] = getArgs(consequent);
		
		
		ArrayList < HashMap < String, String >> result = new ArrayList();

		for (int i = 0; i < subs.size(); i++) {
			
			
			HashMap<String, String> mapClone = (HashMap) subs.get(i).clone();
			HashMap<String,String> newMapClone = (HashMap) newMap.clone();

			for (int j = 0; j < argsAntecedent.length; j++) {
				if (Character.isLowerCase(argsAntecedent[j].charAt(0))) {

					if (!newMapClone.containsKey(argsAntecedent[j])) {

						if (mapClone.containsKey(argsConsequent[j])) {
//							System.out.println(mapClone.get(argsConsequent[j]).toString().charAt(0));
							if (!Character.isLowerCase(mapClone.get(argsConsequent[j]).toString().charAt(0))) {
								newMapClone.put(argsAntecedent[j], (String) mapClone.get(argsConsequent[j]));
							}
						} else {
							if(Character.isUpperCase(argsConsequent[j].charAt(0)))
								newMapClone.put(argsAntecedent[j], argsConsequent[j]);
						}
					}
				}

			}

			result.add(newMapClone);

		}
//		System.out.println(result);
		return result;
	}

	public void printFunc() throws IOException {

		File file = new File("output.txt");

		FileWriter fileWritter = new FileWriter(file.getName(), false);
		BufferedWriter bufferWritter = new BufferedWriter(fileWritter);
		for (int i = 0; i < output.size(); i++) {
			if (output.get(i)) 
				bufferWritter.write("TRUE\n");
			else 
				bufferWritter.write("FALSE\n");
		}
		bufferWritter.close();

	}
	
	
	private String getConsequent(String q) {
		
		String[] splitRule = q.split(IMPLIES);
		
		return splitRule[1];
	}
	
	private HashMap < String, String > HMmerge(String currentPred, String consequent) {
		
		HashMap < String, String > resultHM = new HashMap < String, String > ();
		
		String[] currentPredArg = getArgs(currentPred);
		String[] rightPartRuleArg = getArgs(consequent);
		
		for (int i = 0; i < rightPartRuleArg.length; i++) {
			
			if (!rightPartRuleArg[i].equals(currentPredArg[i])) {
				
			
				if (!Character.isLowerCase(currentPredArg[i].charAt(0))){ 
					
					resultHM.put(rightPartRuleArg[i], currentPredArg[i]);
				}
			}

		}

		return resultHM;
	}

}