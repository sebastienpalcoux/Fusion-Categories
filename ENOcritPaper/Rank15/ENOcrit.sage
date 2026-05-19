def ENOcrit(l):
	pt = l.count(1)
	spt=set(Integer(pt).prime_factors())
	d=sum(i**2 for i in l)
	S=list(set(l))
	S.sort()
	M=[]
	MP=ModularPartitions(l)
	for P in MP:
		S0=list(set(P[0]))
		S0.sort()
		if ENOcritInter(S0,S,spt,pt,d):
			M.append(P)
	if len(M)>0 and len(M)<len(MP) and pt>1:
		print('only need to consider the partitions in ', M)
	return len(M)>0	
	
def ENOcritInter(S0,S,spt,pt,d):
	for i in S0[1:]:
		for p in set(Integer(i).prime_factors())-spt:
			c=0
			for j in S[1:]:
				if j%p!=0 and lcm(i,j)**2 + pt*(i**2) <= d:
					c=1
					break
			if c==0:
				return False
	return True			
	
# generate modular partitions of type l
def ModularPartitions(l):
    d = sum(i^2 for i in l)
    p = l.count(1)
    # assert d % p == 0
    if d % p != 0:
        return []
    U = sorted(set(l))  # unique elements in l
    S = [[p.count(u^2) for u in U] for p in gen_mparts([i^2 for i in reversed(l)], d//p)]
    return sorted(sorted(sum(([u] * q for u, q in zip(U, Qi)), [])
            for Qi in Q) for Q in VectorPartitions([l.count(u) for u in U], parts=S))	
		
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
