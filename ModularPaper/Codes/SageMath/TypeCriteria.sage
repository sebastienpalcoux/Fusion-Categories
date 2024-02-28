# %attach SAGE/TypeCriteria.sage

import copy

## Collect here all the criteria for a type to be the type of a fusion ring (fusion type, as for fusion ring and Grothendieck ring), and explain/prove it.

# pretest is in fusion2.spyx, for pretest, the smallest nontrivial FPdim must be unique


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
