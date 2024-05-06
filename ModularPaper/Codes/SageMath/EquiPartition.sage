## WARNING ####
##### This file is no more updated, it was merged with TypeCriteria ##########


# generate submultisets of list M (sorted in nonincreasing order) with a given sum s
def gen_mparts(M,s,i=0):
    if s==0:
        yield tuple()
        return
    while i<len(M) and M[i]>s:
        i += 1
    prev = 0
    while i<len(M):
        if M[i]!=prev:
            for p in gen_mparts(M,s-M[i],i+1):
                yield p+(M[i],)
        prev = M[i]
        i += 1

# generate modular partitions of type T
def ModularPartitions(T):
    d = sum(i^2 for i in T)
    p = T.count(1)
    #assert d%p==0
    if d%p!=0:
        return []

    U = list(set(T))    # unique elements in T

    S = [ [p.count(u^2) for u in U] for p in gen_mparts([i^2 for i in reversed(T)],d//p) ]
    return sorted( sorted(sum(([u]*q for u,q in zip(U,Qi)),[]) for Qi in Q) for Q in VectorPartitions( [T.count(u) for u in U], parts=S ) )

#ModularPartitions([1, 1, 1, 1, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5])
    
    
'''
sage: %attach EquiPartition.sage
sage: l0=[1,1,1,1,2]
sage: ModularPartitions(l0)
[]									# no solution
sage: l1=[1, 1, 1, 3, 12, 12, 30, 40, 40, 40, 40, 40, 40, 60]
sage: ModularPartitions(l1)
[[[1, 1, 1, 3, 12, 12, 30, 60], [40, 40, 40], [40, 40, 40]]]		# only one solution
sage: l2=[1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4]
sage: ModularPartitions(l2)
[[[1, 1, 1, 1, 4], [2, 2, 2, 2, 2], [2, 4], [2, 4]],			# two solutions
 [[1, 1, 1, 1, 2, 2, 2, 2], [2, 4], [2, 4], [2, 4]]]
sage: l3=[1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 6, 6]
sage: ModularPartitions(l3)
[[[1, 1, 2, 2, 2, 2, 3, 3, 6], [3, 3, 3, 3, 6]],			# three solutions
 [[1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3], [6, 6]],
 [[1, 2, 2, 3, 3, 3, 6], [1, 2, 2, 3, 3, 3, 6]]]
sage: l=[1, 1, 1, 1, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]
sage: %time ModularPartitions(l)
CPU times: user 177 µs, sys: 24 µs, total: 201 µs
Wall time: 202 µs							# very efficient code
[[[1, 1, 1, 1, 4, 4, 4, 4, 4, 4], [5, 5, 5, 5], [5, 5, 5, 5], [5, 5, 5, 5]],
 [[1, 1, 4, 4, 4, 5, 5], [1, 1, 4, 4, 4, 5, 5], [5, 5, 5, 5], [5, 5, 5, 5]]]

'''    

    
    
##############  
   

'''
Conjecture: for all n and for all p, there is N such that for all r>=N with p divides sum_{i=1}^r i^n then there is a (n,p)-equipartition, partition in p parts with same nth power.
'''    
    
'''
# Example usage
lst = [1,1,1,1]
p = 4
partitions = squareequipartition(lst, p)
for partition in partitions:
    print(partition)

'''

''''
# Example usage
l = [1, 1, 1, 1, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]
print(ModularPartitions(l))
'''





############## Assuming G is your finite group defined in SageMath and partition is a dictionary

def check_assumption(M, partition):
    r = len(M)
    '''    
    # Inverse partition for a quick lookup: which group element does an index belong to?
    index_to_group = {}
    for g, indices in partition.items():
        for i in indices:
            index_to_group[i] = g
    '''    
    for g, B_g in partition.items():
        for h, B_h in partition.items():
            gh = g*h  # Group operation in SageMath
            B_gh = partition[gh]
            
            for i in B_g:
                for j in B_h:
                    for k in range(r):
                        # Check if M[i][j][k] is non-zero
                        if M[i][j][k] != 0:
                            # Check if k is in B_gh
                            if k not in B_gh:
                                return False
    return True

'''
# Example
sage: print([L,d])
[[1, 1, 2, 3, 3, 24, 30, 30, 40, 40, 40, 60, 60], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 11]]
sage: print(l)
[0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,1,0,0,1,1,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,2,0,0,0,0,0,0,1,1,0,0,0,0,1,0,0,0,0,0,1,1,0,0,1,0,0,0,1,1,1,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,3,0,0,0,0,0,0,2,1,0,0,0,0,2,0,0,0,0,1,1,1,0,1,1,0,1,0,1,2,1,0,0,0,0,0,0,0,3,0,0,0,0,0,0,1,2,0,0,0,0,1,0,0,0,0,1,1,1,0,1,1,0,1,0,2,1,23,0,0,0,0,0,0,12,12,0,0,0,0,12,0,0,0,0,8,8,8,0,8,8,0,8,0,12,12,3,1,4,4,4,0,3,4,4,4,0,8,8,8,0,8,8,0,8,0,15,15,1,4,4,4,0,8,8,8,0,8,8,0,8,0,15,15,7,8,8,0,8,7,0,8,0,20,20,7,8,0,8,0,20,20,7,0,20,20,0,0]
sage: mat=DoubleMakemat(L,d)
sage: M=mat(l)
sage: G=SymmetricGroup(2)
sage: partition = {G[0]: [0,1,2,3,4,5,6,7,8,9,10], G[1]: [11,12]}
sage: check_assumption(M, partition)
True

'''    

#%attach /home/sebastien/Nutstore Files/SAGE/TypeToNormaliz.sage
def FilterGraded(L,d,LL,partition,e):
	if e==1:
		mat=Makemat(L,d)
	if e==2:
		mat=DoubleMakemat(L,d)
	ll=len(LL[0])	
	V = [var(f'x{i}') for i in range(ll)]
	M=mat(V)
	r=len(d)
	ZV=[]
	for g, B_g in partition.items():
		for h, B_h in partition.items():
			gh = g*h  # Group operation in SageMath
			B_gh = partition[gh]
			for i in B_g:
				for j in B_h:
					for k in range(r):
						if k not in B_gh:
							if 0 not in [i,j,k]: # to avoid non-variable
								v=M[i][j][k]
								if not v in ZV:
									ZV.append(v)
	ZI=[V.index(v) for v in ZV]								
	ZI.sort(); #print(ZI)									
	ZLL=[]
	for l in LL:
		c=0
		for i in ZI:
			if l[i]!=0:
				c=1
				break
		if c==0:
			ZLL.append(l)
	return ZLL																					   
	
'''
sage: [L,d]=[[1,1,2,2,2,2,3,3],[0,1,2,3,4,5,6,7]]
sage: LL=[[0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0,0,0,1,0,0,0,1,0,1,0,0,0,0,0,0,1,1,0,0,0,1,0,0,0,0,0,1,1,1,0,1,0,0,0,0,0,0,0,1,0,0,1,1,1,0,1,0,0,0,0,0,1,1,1,0,0,0,1,1,1,0,0,0,0],[0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0,0,0,1,0,0,0,1,0,1,0,0,0,0,0,0,1,1,0,0,0,1,0,0,0,0,0,1,1,1,1,0,0,0,0,0,1,0,0,0,0,0,1,1,1,1,0,0,0,0,0,0,1,1,1,1,0,0,1,1,1,0,0,0,0]]
sage: G=SymmetricGroup(2)
sage: partition = {G[0]: [0,1,2,3,4,5], G[1]: [6,7]}
sage: GLL=FilterGraded(L,d,LL,partition,1)
[5, 6, 11, 12, 16, 17, 20, 21, 23, 24, 32, 33, 37, 38, 41, 42, 44, 45, 52, 53, 56, 57, 59, 60, 66, 67, 69, 70, 75, 76, 80, 81, 82, 83]
sage: len(LL)
2
sage: len(GLL)
2

'''	


# Script for the modular universal grading criteria:


def ExistenceUniversalGrading(L0):
	L1=[]; LL1=[]
	for l in L0:
		print('0',l)
		if l[-1]==1:			# avoid pointed, as no exclusion
			LL1.append(l)
		else:
			S=TimeFunction(ModularPartitions,l,10)	#10s limit, you can change. The function should be optimize to deal with multiplicity
			if S == 'too slow':
				print('partition too slow')
				LL1.append(l)
			else:
				if len(S)>0:
					L1.append(l)
	return [L1,LL1]
	
def CandidateToExclusion(L1):
	L2=[]; LL2=[]
	for l in L1:
		pt=MultGrp(l)[0][1]				# size of the pointed part
		print('1',l)
		S=ModularPartitions(l)
		for s in S:
			if s[0][1]!=1:	
				if len(s[0])>13:		# regardless grading, we proved that there is no non-trivial perfect up to rank 13
					LL2.append([l,s])
			else:
				if pt>MultGrp(s[0])[0][1]:		# if so, there must be a 1 out of the neutral component, so not a candidate (i.e. B_pt not included in B_e)				
					LL2.append([l,s])	
				else:
					t=MultGrp(s[0])
					c=0
					for tt in t:
						if tt[1]%2==1:		# condition (1) of Theorem 8.1 is satisfied
							L2.append([l,s])	
							c=1
							break
					if c==0:			# none odd mult, so not a candidate
						LL2.append([l,s])
	return [L2, LL2]						# LL2 to be considered later				
					
def Criterion1(L2):	
	L3=[]; LL3=[]
	for l in L2:
		print('2',l)
		c=0
		#t=ListToType(l[0])
		for ll in l[1][1:]:
			t=MultGrp(ll)
			for tt in t:
				if tt[1]==1:			# an entry in a non-neutral component has mult 1, so excluded
					c=1
					break
			if c==1:
				break
		if c==0:
			ll=l[1][0]
			t=MultGrp(ll)
			t0=list(factor(t[0][1])) 		# t[0][1] cannot be 1 because L2 comes from CandidateToExclusion
			if len(t0)==1 and t0[0][1]==1:		# check that the pointed part has prime size
				L3.append(l)
			else:
				LL3.append(l)	
	return [L3,LL3]
	
# Warning: the ones where the pointed part has cardinality non-prime should be considered later
# extra code required

def Criterion2(L3):		
	L4=[]
	for l in L3:
		print('3',l)
		c=0
		ll=l[1][0]
		t=MultGrp(ll)
		p=t[0][1]		# it is a prime as L3 comes from Criterion1
		for tt in t[1:]:
			if tt[0]%p!=0 and tt[1]%p!=0:		# criterion (2)
				c=1
				break
		if c==0:
			L4.append(l)
	return L4

from sage.all import cartesian_product
def ListOfModularizationTypes(L4):							# explain this function in more details in the paper
	L5=[]
	for l in L4:
		print('4',l)
		ll=l[1][0]
		t=MultGrp(ll)
		p=t[0][1]								# p is prime here by previous function
		n=sum([i^2 for i in ll])/p						# n%p==0 as coming from squareequipartition
		LL=[[[1]]]
		c=0
		for [d,m] in t[1:]:
			LLL=[];  #print([d,m])
			if d%p!=0 and n%(d^2)==0:					# second assumption is for the modularization to be half-Frobenius
				#print(m,p,m/p)
				LLL.append([d for i in range(int(m/p))])		# because L4 comes from Criterion2, d%p==0 or m%p==0
			else:	
				k=m//p
				LLL.append([d/p for i in range(p*m)])
				for s in range(1,k+1):
					if n%(d^2)==0:
						LLL1=[d for i in range(s)]
						LLL2=[d/p for i in range(p*(m-s*p))]
						LLL.append(LLL1+LLL2)
			if len(LLL)==0:
				c=1
				break	
			else:						
				LL.append(LLL)	
		if c==0:			
			LL_tuples = [[tuple(inner_list) for inner_list in outer_list] for outer_list in LL]; #print('LL=',LL)
			all_combinations = cartesian_product(LL_tuples)
			merged_lists = [sum(list(map(list, combination)),[]) for combination in all_combinations]; #print(merged_lists)
			LLs=[]
			for ls in merged_lists:
				ls.sort()
				if not ls in LLs:
					print(ls)
					if not(len(ls)>1 and ls[1]>1 and len(list(factor(n)))<=2):		# not(non-trivial and perfect and FPdim = p^a q^b) #add lemma that  it is true
						LLs.append(ls)
			if len(LLs)>0:
				print('new iteration',LLs)
				LLLs=GradingCriteria(LLs)							# iteration process, warning!!! could be long!! Explain
				if len(LLLs)>0:
					L5.append([l,LLLs]); print([l,LLs])						# what about using non-graded criteria also?
	return L5	
	
'''
Bug with:
sage: L4=[[[1, 1, 1, 3, 6, 6, 6, 6, 6, 8, 8, 8, 8, 8, 8], [[1, 1, 1, 3, 6, 6, 6, 6, 6], [8, 8, 8], [8, 8, 8]]]]
'''	
	
			
'''						

....: LL = [[[1, 2], [3, 4]], [[5, 6], [7, 8]]]
....: 
....: # Convert inner lists to tuples to make them hashable
....: LL_tuples = [[tuple(inner_list) for inner_list in outer_list] for outer_list in LL]
....: 
....: # Import the necessary function
....: from sage.all import cartesian_product
....: 
....: # Generate all combinations using cartesian product on tuples
....: all_combinations = cartesian_product(LL_tuples)
....: 
....: # Convert each tuple in the Cartesian product to a list of lists
....: merged_lists = [sum(list(map(list, combination)),[]) for combination in all_combinations]
....: 
....: # Print the results
....: print(merged_lists)
[[1, 2, 5, 6], [1, 2, 7, 8], [3, 4, 5, 6], [3, 4, 7, 8]]
				
'''		
	
# Now must consider L4, LL2 and LL3:

def Rest(LL1,LL2,LL3,L5):
	RL=[]		# rest to consider
	RRL=[]
	RRL.extend(LL1)
	RRL.extend([l[0] for l in LL2])
	RRL.extend([l[0] for l in LL3])
	RRL.extend([l[0][0] for l in L5])
	for ll in RRL:
		if not ll in RL:
			RL.append(ll)		
	RL.sort()
	return RL
	
def GradingCriteria(L0):
	LP=[]; LNP=[]			# remove the one does not passing Theorem4Check, and then move the perfect one at the end
	for l in L0:
		print(l)
		if len(Theorem4Check(l))>0:
			if l[1]>1:
				LP.append(l)
			else:
				LNP.append(l)
	[L1,LL1]=ExistenceUniversalGrading(LNP)	#0
	[L2,LL2]=CandidateToExclusion(L1)	#1
	[L3,LL3]=Criterion1(L2)			#2
	L4=Criterion2(L3)			#3
	L5=ListOfModularizationTypes(L4)	#4
	if len(L5)>0:
		print('Try this by hand', L5)
	RL=Rest(LL1,LL2,LL3,L5)
	RL.extend(LP)
	return RL	
		
# do something for criterion 0 (perfect neutral element)	

# %attach Nutstore/1/SAGE/TimeFunction.sage

def GradingCriteriaTime(l,t):
	ti=TimeFunction(GradingCriteria,[l],t)
	if ti==[]:
		return False
	return True



# Code for theorems 3, 4 in MO https://mathoverflow.net/q/466864/34538


# Function to find all partitions of the list P
def find_partitions2(lst):
    if len(lst) == 1:
        yield [lst]
    else:
        first = lst[0]
        for smaller in find_partitions2(lst[1:]):
            # Insert the first element to each of the sublist
            for i, sublist in enumerate(smaller):
                yield smaller[:i] + [[first] + sublist] + smaller[i+1:]
            # Include the first element as a new sublist
            yield [[first]] + smaller

# Function to check if there's a sublist of M for each partition with distinct m_i for each subset
'''
def check_sublist_for_partitions(M, partitions):
    from itertools import combinations
    
    valid_partitions = []
    for partition in partitions:
        for m_combination in combinations(M, len(partition)):
            valid_for_this_combination = True
            for m_i, subset in zip(m_combination, partition):
                lcm_value = lcm([p-1 for p in subset])
                if m_i < lcm_value / 2:
                    valid_for_this_combination = False
                    break
            if valid_for_this_combination:
                valid_partitions.append([partition,m_combination])
                break  # Once a valid combination is found, move to the next partition
    return valid_partitions
'''    

def check_sublist_for_partitions(M, partitions):
    from itertools import combinations, permutations
    from sage.all import lcm  # Ensure the use of SageMath's lcm function
    
    valid_partitions = []
    checked_combinations = set()  # To avoid redundant checks
    
    for partition in partitions:
        for combination in combinations(M, len(partition)):
            # Generate all permutations of the current combination if not checked
            for m_combination in permutations(combination):
                if m_combination in checked_combinations:
                    continue  # Skip if this permutation was already checked
                
                valid_for_this_combination = True
                for m_i, subset in zip(m_combination, partition):
                    lcm_value = lcm([p-1 for p in subset])
                    if m_i < lcm_value / 2:
                        valid_for_this_combination = False
                        break
                
                # Record this permutation as checked to avoid redundancy
                checked_combinations.add(m_combination)
                
                if valid_for_this_combination:
                    valid_partitions.append([partition, m_combination])
                    break  # Once a valid combination is found, no need to check further permutations for this partition
    return valid_partitions


def MultGrp(l):
	ll=list(set(l))
	ll.sort()
	return [[i,l.count(i)] for i in ll]
    
def Theorem3Check(l):
    t=MultGrp(l)
    s=sum([i^2 for i in l])
    lp=list(factor(s))
    r=len(l)
    p=lp[-1][0]
    tm=max([tt[1] for tt in t])
    return p<=2*tm+1
    
def Theorem4Check(l):
	if l[-1]==1:
		return ['ok, pointed']
	n=sum([i^2 for i in l])
	P0=list(factor(n))
	P=[a[0] for a in P0 if a[0] not in [2,3]]
	if P==[]:
		return [True]
	t=MultGrp(l)
	M=[a[1] for a in t if a[1]!=1]; #print(P,M)
	# Generate all partitions
	partitions = list(find_partitions2(P)); #print(partitions)
	# Filter partitions based on the condition
	valid_partitions = check_sublist_for_partitions(M, partitions)
	return valid_partitions
	
def sublists_with_sum_of_squares(l, n):
	global LL
	LL=[]
	sublists_with_sum_of_squares_inter(l, n, [])
	return LL
	
def sublists_with_sum_of_squares_inter(l, n, sol):
	global LL
	if n==0:
		if not sol in LL:
			LL.append(sol)
	for k in range(len(l)):
		i=l[k]
		if n>=i**2:
			m=n-i^2
			soll=[j for j in sol]
			soll.append(i)
			sublists_with_sum_of_squares_inter(l[k+1:], m,soll)	
			
			
########## OLD Script ########


'''
# Example usage
l = [1, 2, 2, 3, 4, 5, 6]
first_part = [2, 3]
remaining = list_difference(l, first_part)

print(remaining)  # Output: [1, 2, 4, 5, 6]
'''

'''
def squareequipartition_into_four_parts(lst):
    n = len(lst)
    all_partitions = []
    if sqsum(lst)%4!=0:
        return []
    l4=sqsum(lst)/4
    # The first loop chooses the size of the first part
    for i in range(1, n-2):
        for firstpart in combinations(lst, i):
            first_part = list(firstpart); first_part.sort()
            if sqsum(first_part)==l4:
                remaining_elements_after_first = list_difference(lst, first_part)
                # The second loop chooses the size of the second part from the remaining elements
                for j in range(1, n-i-1):
                    for secondpart in combinations(remaining_elements_after_first, j):
                        second_part = list(secondpart); second_part.sort()
                        if sqsum(second_part)==l4:
                            remaining_elements_after_second = list_difference(remaining_elements_after_first, second_part)
                            # The third loop chooses the size of the third part from the remaining elements
                            for k in range(1, n-i-j):
                                for thirdpart in combinations(remaining_elements_after_second, k):
                                    third_part = list(thirdpart); third_part.sort()
                                    if sqsum(third_part)==l4:
                                        fourth_part = list_difference(remaining_elements_after_second, third_part); fourth_part.sort()
                                        llll=[first_part, second_part, third_part, fourth_part]; llll.sort()
                                        # Now we have all four parts
                                        if not llll in all_partitions:
                                            all_partitions.append(llll)
    
    return all_partitions

# Example
l = [1, 2, 3, 4, 5, 6]
partitions = partition_into_four_parts(l)
print(f"Total partitions: {len(partitions)}")
for p in partitions:
    print(p)




from itertools import combinations

def sqsum(lst):
    """Calculate the square sum of a list."""
    return sum(x**2 for x in lst)

def list_difference(lst1, lst2):
    """Return the difference between two lists."""
    return [item for item in lst1 if item not in lst2]
   
'''


'''


from itertools import combinations

def list_difference(lst, subtract):
    """
    Return a new list that is the result of subtracting all elements in `subtract` from `lst`.
    Preserves the order of `lst` and handles duplicates correctly.
    """
    subtract = list(subtract)  # Make a mutable copy
    return [item for item in lst if not (item in subtract and subtract.remove(item) is None)] 

def sqsum(l):
	return sum(i**2 for i in l)	 
 
def find_partitions(remaining, target_sum, current_partition, all_partitions, p, depth=0):
    if depth == p - 1:
        if sqsum(remaining) == target_sum:
            current_partition.append(remaining)
            all_partitions.append(current_partition)
        return
    
    for i in range(1, len(remaining) - (p - depth) + 2):
        for part in combinations(remaining, i):
            part_list = list(part); part_list.sort()
            if sqsum(part_list) == target_sum:
                remaining_after_part = list_difference(remaining, part_list)
                # Create a new partition that includes this part.
                new_partition = current_partition + [part_list]
                find_partitions(remaining_after_part, target_sum, new_partition, all_partitions, p, depth + 1)

def squareequipartition(lst, p):
    if len(lst) < p or sqsum(lst) % p != 0:
        return []
    
    target_sum = sqsum(lst) // p
    all_partitions = []
    find_partitions(lst, target_sum, [], all_partitions, p)
    
    # Remove duplicates
    all_partitions = [list(map(list, part)) for part in set(tuple(map(tuple, sorted(part))) for part in all_partitions)]
    
    return all_partitions

def ModularPartitions(l):
    if l[-1]==1:
        return [[[1] for i in l]]
    i=1; le=len(l)
    while i<le and l[i]==1:
        i+=1
    return squareequipartition(l,i)
'''  			

