# Read("GroupTheoretical.gap");

# This section presents the GAP code used in this paper. We begin with the code that determines the type of the group-theoretical fusion category $\mathcal{C}(G, 1, H, 1)$; see \S\ref{sec:grpth}.

GroupTheoreticalType := function(G, H)	  # trivial 3-cocycle and 2-cochain
  local doubleCosets, dims, g, Hg, intersection, index, reps, chi, R;
  doubleCosets := DoubleCosets(G, H, H);
  dims := [];
  R:=List(doubleCosets, Representative);
  for g in R do
    Hg := ConjugateSubgroup(H, g);        # gHg^{-1}
    intersection := Intersection(H, Hg);  # H n gHg^{-1} = H^g
    index := Index(H, intersection);      # [H : H^g] 
    reps := Irr(intersection);            # irreducible characters
    for chi in reps do
      Add(dims, index * chi[1]); # Add(dims, index * chi[1]); 
    od;
  od;
  Sort(dims);
  return dims;
end;;

# We illustrate this with the following example:

# gap> G := AlternatingGroup(5);
# gap> H := AlternatingGroup(4);
# gap> GroupTheoreticalType(G, H);
# [ 1, 1, 1, 3, 4, 4, 4 ]

#The following code, slightly more involved, also provides the duality:

GroupTheoreticalTypeDuality := function(G, H)
  local doubleCosets, dims, simples1, simples2, g, Hg, intersection, index,
        reps, chi, R, lR, perm, Rh, gp, h1, hh, a, ConjInter, i, s, CC, dual, l;
  doubleCosets := DoubleCosets(G, H, H);
  simples1 := []; dims:=[];
  R:=List(doubleCosets, Representative); lR:=Length(R);;
  # permutation representatives of g^-1
  perm:= List(R, g -> Position(doubleCosets, DoubleCoset(H, g^-1, H)));  
  # list of h1 with gp = h1g^-1h2
  Rh:=List([1..lR], i -> First(Cartesian(H, H), p -> p[1] * (R[i])^-1 * p[2] = R[perm[i]])[1]);   
  for i in [1..lR] do
    g:=R[i]; 		
    Hg := ConjugateSubgroup(H, g^-1);     # gHg^{-1}
    intersection := Intersection(H, Hg);  # H n gHg^{-1} = H^g
    index := Index(H, intersection);      # [H : H^g] 
    reps := Irr(intersection);            # irreducible characters
    for chi in reps do
      Add(simples1, [index * chi[1],i, intersection, chi]); 
    od;
  od;
  Sort(simples1); 
  simples2:=[];
  for s in simples1 do
    CC:=List(ConjugacyClasses(s[3]),Representative);
    Add(simples2, [s[1],s[2],s[3], List(CC, a-> a^(s[4]))]);
  od;  
  dual:=[];		# Computation of the duality permutation list
  for s in simples1 do
    hh:=Rh[s[2]] * (R[s[2]])^-1;
    ConjInter:=ConjugateSubgroup(s[3], hh^-1);
    CC:=List(ConjugacyClasses(ConjInter),Representative);
    l:=[s[1],perm[s[2]],ConjInter,List(CC, a->ComplexConjugate(((hh)^-1 * a * hh)^(s[4])))];  
    Add(dual,Position(simples2,l)-1);   # -1 to align with Python convention
    Add(dims,s[1]);
  od;  
  return [dims,dual];
end;;

# We now apply it to the preceding example:

# gap> GroupTheoreticalTypeDuality(G, H);
# [ [ 1, 1, 1, 3, 4, 4, 4 ], [0, 2, 1, 3, 4, 5, 6] ]


# Finally, the following code finds all groups $G$ and subgroups $H$ such that $\mathcal{C}(G,1,H,1)$ has type \texttt{t}, and also computes the corresponding duality.

FindGroupSubgroup := function(t)
    local n, i, j, G, subgroups, H, result, TD;
    n:=Sum(List(t, i -> i^2));; result := [];; 
    for i in [1..NrSmallGroups(n)] do
        G := SmallGroup(n, i);;
        subgroups := List(ConjugacyClassesSubgroups(G), Representative);;
        for j in [1..Length(subgroups)] do
            H := subgroups[j];;
            if GroupTheoreticalType(G, H) = t then
                TD:=GroupTheoreticalTypeDuality(G,H);
                Add(result, [i,StructureDescription(G), j, StructureDescription(H),TD]);
            fi;
        od;
    od;
    return result;
end;;

# We proceed by applying it to the types $[1,1,2,3,3,6]$ and $[1,1,2,2,5,5]$:

# gap> FindGroupSubgroup([1,1,2,3,3,6]);
# [ [ 5, "A5", 6, "S3", [ [ 1, 1, 2, 3, 3, 6 ], [0, 1, 2, 3, 4, 5] ] ] ]
# gap> FindGroupSubgroup([1,1,2,2,5,5]);
# [ [ 5, "A5", 7, "D10", [ [ 1, 1, 2, 2, 5, 5 ], [0, 1, 2, 3, 4, 5] ] ] ]

# "D10" denotes the dihedral group of order 10, which is also commonly written as D_5.
