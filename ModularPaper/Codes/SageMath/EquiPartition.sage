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
	ZI.sort(); print(ZI)									
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