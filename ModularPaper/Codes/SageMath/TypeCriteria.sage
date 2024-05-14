# %attach SAGE/TypeCriteria.sage

import copy

## Collect here all the criteria for a type to be the type of a fusion ring (fusion type, as for fusion ring and Grothendieck ring), and explain/prove it.


def TypeCriteria(l,ti=None):
	if l==[1]:
		return True
	if ti is None:
		ti = 0.01	
	t=ListToType(l)
	return SmallPerfect(l) and GcdCriterion(l) and TypeTest(t) and LocalCriterionAll(t,ti)	# here are the three general criteria we use, some more (like pretest below) could be added later

def TypesCriteria(L,ti=None):
	if ti is None:
		ti = 0.01
	LL=[]
	for l in L:
		print(l)
		if TypeCriteria(l,ti):
			LL.append(l)
	return LL		
	
def ListToType(l):
	t=MultGrp(l)
	if t[0][1]==1:
		return t
	else:
		tt=[[1,1]]
		tt.extend(t)
		tt[1][1]-=1
		return tt
		
def SmallPerfect(l):
	if len(l)==1 or l[1]==1:	# dedicated to non-trivial perfect only
		return True
	else:
		return len(MultGrp(l))>3 and len(list(factor(sum([i^2 for i in l]))))>2	
		
def BadPerfect(L):
	BP=[]
	for l in L:
		if len(l)>1 and l[1]>1 and len(list(factor(sum([i^2 for i in l]))))<=2:
			BP.append(l)
	return BP		
		
def SmallPerfectRing(l):
	if len(l)==1 or l[1]==1:	# fusion ring version as the assumption len(list(factor(sum([i^2 for i in l]))))>2 is proved only at the categorical level
		return True
	else:
		return len(MultGrp(l))>3

def TypeCriteriaRing(l,ti=None):
	if l==[1]:
		return True
	if ti is None:
		ti = 0.01	
	t=ListToType(l)
	return SmallPerfectRing(l) and GcdCriterion(l) and TypeTest(t) and LocalCriterionAll(t,ti)
	
def TypesCriteriaRing(L,ti=None):
	if ti is None:
		ti = 0.01
	LL=[]
	for l in L:
		print(l)
		if TypeCriteriaRing(l,ti):
			LL.append(l)
	return LL						

def GcdCriterion(l):	# made for non-trivial perfect, otherwise return True
	if len(l)==1 or l[1]==1:
		return True
	sl=[]
	for i in l[1:]:
		if i<l[1]**2:
			sl.append(i)
	return gcd(sl)==1		
	
def GcdCriterionDumb(l):	# above function is much more efficient
	if len(l)==1 or l[1]==1:
		return True
	return gcd(l[1:])==1

def TypeMult(TT):		# this test is useful when all FPdims (of non-trivial) are mult. of some n except one (to be generalized)
	T=TypeToType2(TT)
	R=[]
	N=[t[0] for t in T[1:]]
	if gcd(N)!=1:				# here is a possible entry for a more general criterion (gcd(N)!=1, or gcd(N minus one element)!=1, or minus two elements etc...)
		return []
	else:
		for t in T[1:]:
			n=t[0]
			Nn=copy.deepcopy(N)
			Nn.remove(n)
			g=gcd(Nn)		# note that gcd(g,n)=gcd(N)=1, in particular, n in invertible in Z_g
			R.append(t+[g])
	return(R)

def TypeToType2(TT):
	if TT[1][0]==1:
		T=copy.deepcopy(TT[1:])
		T[0]=[1,TT[1][1]+1]
	else:
		T=TT
	return T
		
def TypeTest(T):		# T is of the form [[1,1],[a,n],...] with a>1
	if T[1][0]==1:
		return True
	R=TypeMult(T)
	for r in R:
		d=r[0]
		g=r[2]
		m=d**2-1						#
		C=[[1,1]]
		if not (r[1]==1 and r[2]!=1):
			for rr in R:
				gg=rr[2]
				if rr!=r and gg!=1:
					dd=rr[0]
					aa=(-1/dd)%gg
					m-=aa*dd
					C.append([dd,aa])
			#print(r,C,m)
			if m<0:
				return False
		else:
			a=(d-1/d)%(g**2)
			m-=d*a						#
			C.append([d,a])	
			for rr in R:
				gg=rr[2]
				if rr!=r and gg!=1:
					dd=rr[0]
					k=(-1/(dd*g))%gg
					m-=k*g*dd			#
					C.append([dd,k*g])
			#print(r,C,m)
			if m<0:
				return False
	return True


# if c=0 then non-dual case, if c=1 then dual case
# Usual case is g=1. Use g>1 only when c=1 and all mult. of g except d1		
# T should start by [1,1] (if necessary) put [1,n] after. 
# if g!=1, then c=1, so d1=d2, and we do not consider the decomposition of d1*d2 but b1*(all basic elements of FPdim d2), where FPdim(b1)=d1
# see note book 02/04/2022

					
def LocalDecomposition(T, d1, d2, c, g):
	global SSL
	SSL=[]
	L=[]
	cc=c
	if d1 != d2:	# to avoid mistake
		cc=0
	L.append([1,cc])	
	mu=1
	if g!=1:
		for t in T:
			if t[0]==d2:
				mu=t[1]
				break
	m=mu*d1*d2-cc
	dim=[t[0] for t in T[1:]]
	dim.remove(d1)
	a=(mu*d1-1/d1)%(g**2)
	q=(m-a)//(d1*(g**2))
	for i in range(int(q+1)):
		LL=copy.deepcopy(L)
		#if i!=0 or a!=0:
		LL.append([d1,a+i*(g**2)])
		LocalCriterionInter(dim,m-d1*(a+i*(g**2)),g,LL)
	SSL.sort()
	return SSL

def LocalCriterion(TT, d, m, g):
	global SSL
	T=TypeToType2(TT)	# we do that here because TT is of the form [[1,1],[a,n],...] with a>=1, so if a=1 then T is of the form [[1,n+1], ...] 
	SSL=[]
	L=[]
	L.append(T[0])
	m1=T[0][1]
	mm=m*d**2-m1
	dim=[t[0] for t in T[1:]]
	dim.remove(d)
	a=(m*d-m1/d)%(g**2)
	q=(mm-a)//(d*(g**2))	# why not always int here?
	for i in range(int(q+1)):
		LL=copy.deepcopy(L)
		LL.append([d,a+i*(g**2)])
		LocalCriterionInter(dim,mm-d*(a+i*(g**2)),g,LL)
	SSL.sort()
	return SSL



def LocalCriterionInter(dim, m, g, L):
	global SSL
	if m>=0 and len(dim)>0:
		d=dim[-1]
		ddim=copy.deepcopy(dim)
		ddim.remove(d)
		q=m//(d*g)			# Warning: we should have c=1, to be improved
		for i in range(int(q+1)):
			LL=copy.deepcopy(L)
			LL.append([d,i*g])
			LocalCriterionInter(ddim,m-i*d*g,g,LL)
	elif m==0:
		sL=copy.deepcopy(L)
		sL.sort()
		SSL.append(sL)

# %attach Nutstore/1/SAGE/TimeFunction.sage

def LocalCriterionAll(T,t):
	R=TypeMult(T)
	for l in R:
		d=l[0]
		m=l[1]
		g=l[2]
		if g>1:
			ti=TimeFunction4(LocalCriterion,T,d,m,g,t)
			if ti==[]:
				return False
	return True

# Example: [[1, 1], [6, 3], [15, 3], [21, 1], [70, 2], [105, 3]] is excluded by TypeTest but not LocalCriterion at 30s

def isomorphicclasss(M, T, d):
	t=len(T)
	ra=sum([tt[1] for tt in T])
	c=1
	LM=[M]
	for ii in range(1,t):
		r=T[ii][1]
		LLM=[]
		G=SymmetricGroup(r)
		for g in G:
			a=0
			gm=g**-1
			for rr in range(r):
				if not d[c+g(rr+1)-1]-c == g(d[c+rr]-c+1)-1:
					a=1
					break
			if a==0:
				for MM in LM:
					MMM=[matrix([[MM[g(k-c+1)-1+c][g(j-c+1)-1+c][g(i-c+1)-1+c] for i in range(ra)] for j in range(ra)]) for k in range(ra)]
					print(g,c,ra,MM,MMM)
					if MMM not in LLM:
						LLM.append(MMM)
		LM=LLM
		c+=r
	return LM
	
	
#############	IMPORTANT	  ####################
#############	MODULAR SECTION   ###################

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
    return  sorted( sorted(sorted(sum(([u]*q for u,q in zip(U,Qi)),[])) for Qi in Q) for Q in VectorPartitions( [T.count(u) for u in U], parts=S ) )   

#ModularPartitions([1, 1, 1, 1, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5])
    
    
'''
sage: %attach TypeCriteria.sage
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
					t=MultGrp(s[0]); print(t)
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
		n=sum([i^2 for i in ll])//p						# n%p==0 as coming from ModularPartition # warning /p makes mistake, need //p (otherwise integer like 10.0)
		LL=[[[1]]]
		c=0
		for [d,m] in t[1:]:
			LLL=[];  #print([d,m])
			if d%p!=0 and n%(d^2)==0:					# second assumption is for the modularization to be half-Frobenius
				#print(m,p,m//p)
				LLL.append([d for i in range(m//p)])		# because L4 comes from Criterion2, d%p==0 or m%p==0
			else:	
				k=m//p
				LLL.append([d//p for i in range(p*m)])
				for s in range(1,k+1):
					if n%(d^2)==0:
						LLL1=[d for i in range(s)]
						LLL2=[d//p for i in range(p*(m-s*p))]
						LLL.append(LLL1+LLL2)
			if len(LLL)==0:
				c=1
				break	
			else:						
				LL.append(LLL)	
		if c==0:			
			LL_tuples = [[tuple(inner_list) for inner_list in outer_list] for outer_list in LL]; #print('LL=',LL)
			all_combinations = cartesian_product(LL_tuples); # SageMath can make float here, corrected below.
			merged_lists = [sum(list(map(list, combination)),[]) for combination in all_combinations]
			merged_lists_int = [[int(num) for num in sublist] for sublist in merged_lists]; #print('merged_lists_int',merged_lists_int)
			LLs=[]
			for ls in merged_lists_int:
				ls.sort(); #print('ls',ls)
				if not ls in LLs:
					#print(factor(n))
					if not(len(ls)>1 and ls[1]>1 and len(list(factor(n)))<=2):		# not(non-trivial and perfect and FPdim = p^a q^b) #add lemma that  it is true
						#print('yes')
						LLs.append(ls)
			#print('LLs',LLs)			
			if len(LLs)>0:
				print('new iteration',LLs)
				LLLs=GradingCriteria(LLs)							# iteration process, warning!!! could be long!! Explain
				if len(LLLs)>0:
					L5.append([l,LLLs]); #print([l,LLs])						# what about using non-graded criteria also?
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
	LP=[]; LNP=[]			# remove the one does not passing Theorem4Check and TypeCriteria, and then move the perfect one at the end
	for l in L0:
		print(l)
		if len(Theorem4Check(l))>0 and TypeCriteria(l):		# by default 0.01s for LocalCriterion to be quick as most of those covered by 0.1 or 1s are also by 0.01s
			if l[1]>1:					# later add Burciu-Palcoux Burnside-ilke result (i.e. perfect non-trival modular integral implies no powerless prime factor)
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
	RL=Rest(LL1,LL2,LL3,L5); #print('L1',L1,'LL1',LL1,'LL2',LL2,'LL3',LL3,'L5',L5)
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


####################### END OF MODULAR SECTION ################
###############################################################



### Function not yet included in TypeCriteria ###
# pretest is in fusion2.spyx, for pretest, the smallest nontrivial FPdim must be unique

def pretest(T):
	global Z
	Z=0
	dim=[T[i][0] for i in range(1,len(T)) for j in range(T[i][1])]
	l=len(dim)
	M=[[-1 for j in dim] for i in dim]
	pretestrec(dim, list(range(l)), M, 0)
	return Z==1


def deltaminus(n):
	if n==-1:
		return 0
	else:
		return n

def pretestrec(dim,rest,M,n):
	global Z
	l=len(dim)#; print([rest,n])
	m=dim[0]*dim[n]
	rrest=rest[:]
	if rest==[]:
		Z=1#; print(M)											# modified here for a quick pretest to be included in main (to be update later)
	elif Z==0:												# modified	
		rrest.remove(n)
		if n==0:
			r=m-1
		else:
			r=m-sum([dim[i]*deltaminus(M[i][n]) for i in range(l)])
		if r>=0:
			R=[]
			for i in range(l):
				if M[i][n]==-1:
					R.append(i)
			lR=len(R)
			RR=[min(r//dim[i],dim[0]*min(dim[i],dim[n])//max(dim[i],dim[n]))+1 for i in R]
			P=prod(RR)			# the use of multibase is not optimal, it is ok for pretest, but not for an extension
			for i in range(P):
				if Z==0:											#modified
					L=multibase(i,RR)
					if r==sum([dim[R[j]]*L[j] for j in range(lR)]):
						MM=copy.deepcopy(M)
						rrrest=rrest[:]
						for k in range(lR):
							MM[R[k]][n]=L[k]
							MM[n][R[k]]=L[k]
						b=0						
						for k in range(lR):
							if Z==0:								#modified
								a=0
								for j in range(l):
									if MM[R[k]][j]==-1 and Z==0:				#modified	
										pretestrec(dim,rrrest, MM, R[k])
										a=1
										break
								if a==0 and R[k]!=0:
									if dim[0]*dim[R[k]]==sum([MM[R[k]][ii]*dim[ii] for ii in range(l)]):
										if R[k] in rrrest:
											rrrest.remove(R[k])
									else:
										b=1
										break	
								if a==1 or b==1:
									break
							if a==0 and b==0 and Z==0:						#modified
								if rrrest!=[]:	
									pretestrec(dim,rrrest, MM, rrrest[0])
								else:
									Z=1#; print(MM)						#modified
									
									
### Appendix ###


import time
import copy
from multiprocessing import Process

def TimeFunction(F,M,t):
	def function():
		F(M)
	p1 = Process(target=function)
	p1.start()
	p1.join(t)
	if p1.is_alive():
		p1.terminate()
		return 'too slow'
	else:
		return F(M)


def TimeFunction4(F,a1,a2,a3,a4,t):
	def function():
		F(a1,a2,a3,a4)
	p1 = Process(target=function)
	p1.start()
	p1.join(t)
	if p1.is_alive():
		p1.terminate()
		return 'too slow'
	else:
		return F(a1,a2,a3,a4)


																	
