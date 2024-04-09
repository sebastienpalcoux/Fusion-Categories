from itertools import combinations

def list_difference(lst, subtract):
    """
    Return a new list that is the result of subtracting all elements in `subtract` from `lst`.
    Preserves the order of `lst` and handles duplicates correctly.
    """
    subtract = list(subtract)  # Make a mutable copy
    return [item for item in lst if not (item in subtract and subtract.remove(item) is None)]
'''
# Example usage
l = [1, 2, 2, 3, 4, 5, 6]
first_part = [2, 3]
remaining = list_difference(l, first_part)

print(remaining)  # Output: [1, 2, 4, 5, 6]
'''
def sqsum(l):
	return sum(i**2 for i in l)	 


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
'''
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

def squareequipartitiontype(l):
    if l[-1]==1:
        return [[[1] for i in l]]
    i=1; le=len(l)
    while i<le and l[i]==1:
        i+=1
    return squareequipartition(l,i)

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

# Assuming G is your finite group defined in SageMath and partition is a dictionary

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
	L1=[]
	for l in L0:
		print('0',l)
		S=squareequipartitiontype(l)
		if len(S)>0:
			L1.append(l)
	return L1
	
def CandidateToExclusion(L1):
	L2=[]; LL2=[]
	for l in L1:
		print('1',l)
		S=squareequipartitiontype(l)
		for s in S:
			if s[0][1]!=1:				# if so, there must be a 1 out of the neutral component, so not a candidate
				LL2.append([l,s])	
			else:
				t=ListToType(s[0])
				c=0
				if t[1][1]%2==0:
					L2.append([l,s])
					c=1
				else:
					for tt in t[2:]:
						if tt[1]%2==1:
							L2.append([l,s])
							c=1
							break
				if c==0:			# none odd mult, so not a candidate
					LL2.append([l,s])
	return [L2, LL2]					# LL2 to be considered later				
					
def Criterion1(L2):	
	L3=[]; LL3=[]
	for l in L2:
		print('2',l)
		c=0
		t=ListToType(l[0])
		for ll in l[1][1:]:
			lll=[1]
			lll.extend(ll)
			t=ListToType(lll)
			for tt in t[1:]:
				if tt[1]==1:
					c=1
					break
			if c==1:
				break
		if c==0:
			ll=l[1][0]
			t=ListToType(ll)
			t0=list(factor(t[1][1]+1)) #print(t0)
			if len(t0)==1 and t0[0][1]==1:	
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
		t=ListToType(ll)
		c=0
		if t[1][0]!=1:
			c=1
			print(l, 'perfect apply (0)')
		else:
			p=t[1][1]+1
			for tt in t[2:]:
				if tt[1]==1 and tt[0]%p!=0:		# criterion (2)
					c=1
					break
		if c==0:
			L4.append(l)
	return L4
	
# Now must consider L4, LL2 and LL3:

def Rest(LL2,LL3,L4):
	RL=[]		# rest to consider
	RRL=[]
	RRL.extend(LL2)
	RRL.extend(LL3)
	RRL.extend(L4)
	for l in RRL:
		ll=l[0]
		if not ll in RL:
			RL.append(ll)
	RL.sort()
	return RL
	
def AllCriteria(L0):		# please exclude pointed to avoid problem...
	L1=ExistenceUniversalGrading(L0)	#0
	[L2,LL2]=CandidateToExclusion(L1)	#1
	[L3,LL3]=Criterion1(L2)			#2
	L4=Criterion2(L3)			#3
	RL=Rest(LL2,LL3,L4)
	return RL	
		
# do soemthing for criterion 0 (perfect neutral element)	

# %attach Nutstore/1/SAGE/TimeFunction.sage

def AllCriteriaTime(l,t):
	ti=TimeFunction(AllCriteria,[l],t)
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
	n=sum([i^2 for i in l])
	P0=list(factor(n))
	P=[a[0] for a in P0 if a[0] not in [2,3]]
	t=MultGrp(l)
	M=[a[1] for a in t if a[1]!=1]; #print(P,M)
	# Generate all partitions
	partitions = list(find_partitions2(P)); #print(partitions)
	# Filter partitions based on the condition
	valid_partitions = check_sublist_for_partitions(M, partitions)
	return valid_partitions

