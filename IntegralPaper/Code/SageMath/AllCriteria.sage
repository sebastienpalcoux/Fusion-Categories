# %attach SAGE/AllCriteria.sage
# %attach Nutstore/1/SAGE/AllCriteria.sage

### WARNING: if N is the fusion data of a fusion ring, then N[i][j][k]=N_{i,j}^k, 
### BUT matrix(N[i]) is NOT the i-th fusion matrix M_i but its transpose, because M_i = (N_{i,j}^k)_{k,j}

UCF=UniversalCyclotomicField()
import time
import copy
from multiprocessing import Process
import os
import re

def CheckingList(L,t):
	l=len(L)
	for i in range(l):
		print([i])
		M=L[i]
		def function():
			Checking(M)
		p1 = Process(target=function)
		p1.start()
		p1.join(t)
		if p1.is_alive():
			p1.terminate()
			print('too slow')

def FPdims(M):
	return [matrix(m).norm() for m in M]

def FPdim(M):
	L=FPdims(M)
	return sum([i**2 for i in L])

def NormPoly(M): # made for radial matrix (operator norm = spectral radius)
	m=matrix(M)
	d=m.norm()					# need better approx
	L=list(factor(m.minpoly()))
	for l in L:
		if abs(l[0](d))<0.0000001:	# make it better
			return l[0]

def NormField(M): # made for radial matrix (operator norm = spectral radius)
	p=NormPoly(M)
	K.<a> = NumberField(p)
	return K

def IsoField(K,L):
	if K.degree() != L.degree():
		return False
	else:
		return Hom(K,L).order()!=0


def Duality(S):
	l=len(S)
	L=[]
	for i in range(l):
		for j in range(l):
			if S[i][j][0]!=0:
				L.append(j)
	return L

def IsInt(M):
	r=len(M)
	for i in range(r):
		for j in range(r):
			for k in range(r):
				a=M[i][j][k]
				if imaginary(a)!=0 or floor(a) != a:
					print([i,j,k],a.n())
					return False
	return True

def Axioms(M):
	#if not IsInt(M):	#useless for usual request
	#	return False
	d=Duality(M)#print(d)
	r=len(M)
	for i in range(r):
		for j in range(r):
			if not {M[0][i][j],M[i][0][j],M[d[i]][j][0],M[j][d[i]][0]}=={kronecker_delta(i,j)}:
				print([i,j])
				return False
			for k in range(r):
				if not len({M[i][j][k],M[d[i]][k][j],M[k][d[j]][i]})==1:
					print([i,j,k])
					return False
				for t in range(r):
					if not sum([M[i][j][s]*M[s][k][t] for s in range(r)])==sum([M[j][k][s]*M[i][s][t] for s in range(r)]):
						print([i,j,k,t],[sum([M[i][j][s]*M[s][k][t] for s in range(r)]),sum([M[j][k][s]*M[i][s][t] for s in range(r)])])
						return False
	return True
	
def IsAssociative(M):
	d=Duality(M)
	r=len(M)
	for i in range(r):
		for j in range(r):
			for k in range(r):
				for t in range(r):
					A=sum([M[i][j][s]*M[s][k][t] for s in range(r)])
					B=sum([M[j][k][s]*M[i][s][t] for s in range(r)])
					if not A==B:
						print([i,j,k,t],[A,B])
						return False
	return True	

def multibase(n, s):
	l=len(s)
	b=[]
	m=n
	for v in range(l):
		a=prod([s[i] for i in range(l-v-1)])
		c=int(m/a)
		m=m-a*c
		b.append(c)
	b.reverse()
	return b	

def Checking(M):
	if not Axioms(M):
		return 'not a fusion ring'
	print('FPdim  ≃ ',FPdim(M))
	print('FPdims  ≃ ',FPdims(M))	
	r=len(M)
	if simpletest(M):
		print('simple')
	if not NoSpectrumCriterion2(M):	#NoSpectrumCriterion2(M) and OneSpectrumCriterion2(M) and OstrikInequality(M) and Lagrange(M)
		print('non-Czero')
	if not OneSpectrumCriterion2(M):
		print('non-Cone')
	if not PositiveCo(M,3):		# it is an improvment of Schur, working well on NC case, but Schur quicker...
		print('non-3-positive')
	if not OstrikInequality(M):		# also ok for NC
		print('non-Ostrik')
	if not ExtendedCyclo(M):
		print('non-extended-cyclo')
		if NonCo(M):
			if not CycloFormalCodegrees(M):
				print('non-CycloFormalCodegrees')
			else:
				print('NC, so check on dims')
		return 'non-extended-cyclo'	# Extended cyclotomic criterion
	if not ConductorCriterion(M):
		print('non-ConductorCriterion')			
	if not FrobeniusType(M,1,1):
		print('non-1-FrobType')
	if not Lagrange(M):
		print('non-Lagrange')
	if not PseudoUnitaryDrinfeld(M):
		print('non-PseudoUnitaryDrinfeld')
	if not DnumberCrit(M):
		print('non-d-number')
	if NonCo(M):
		if not ExtendedCyclo(M):
			print('non-cyclo', 'check on dims', 'or check irreducibility of the min poly')
		print('non-commutative')
		return('non-commutative')
	if not SphericalDrinfeld(M):
		print('non-SphericalDrinfeld')
	if not PivotalDrinfeld(M):
		print('non-PivotalDrinfeld')
	if not FrobeniusType(M,1,2):
		print('non-1/2-FrobType, so not modular cat')
	B=Burnside(M); DB=DualBurnside(M)	
	if not B:
		print('non-Burnside, so not weakly-int cat')
	if not DB:
		print('non-dual-Burnside, so not perfect int modular cat')
	if not B==DB:
		print('not modular cat')			
	if not Isaacs(M,0,1,1):
		print('non-Isaacs')
'''

Some criteria not yet in the list:
- (ConductorCriterion) the cyclotomic conductor of the formal codegree must divide the one of the FPdims
- (Burciu's Burnside) weakly integral fusion category: FPdim(x)>1 implies det(M_x) nonzero, i.e. zero eigenvalue, i.e. in the row.
- (Burciu) Conjecture: (c_1/c_j)/(c'_1/c'_j) is an algebraic integer, for all fusion subring and all corresponding j (what about this quotient out of the subtable?)
- Statement: on a (pseudo-unitary) Grothendieck ring then for all i, det(M_i) in {-1, 0, 1}. ##False## PSU(3)_4,  Maybe true for modular (no counter-ex in Gert dataset). Question: Is PSU(3)_4 modular? (excluded by preSmatrix). Tell Andrew
- (Andrew conjecture): pseudo-unitary Grothendieck ring: FPdim(M_i) not algebraic unit implies det(M_i) = 0
'''

def IsQuadratic(M):		# def: the group of the pointed part acts transitively on the non-pointed part
	r=len(M)
	G=[]
	for i in range(r):
		s=sum(sum(l) for l in M[i])
		if s==r:
			G.append(i)
	for i in range(r):
		if not i in G:
			L=[]
			for j in G:
				k=M[i][j].index(1)
				if not k in L:
					L.append(k)
			return len(G)+len(L)==r			

def Statement(M):
	L=[matrix(m).determinant() for m in M]
	for x in L:
		if not x in [-1,0,1]:
			return False
	return True
'''
def AndrewPseudoUnitary(M):
'''

def ModularCriterion(M,ep):		# positive case (ok for pseudo-unitary) # very nice, it contains (1/2)-Frobenius without requiring cyclo. Moreover, should be used before SelfTransposable function.
	if NonCo(M):
		return False
	FC=FormalCodegreesCoNum(M)
	FC.sort()
	Di=[matrix(m).norm() for m in M]
	PF=sum([x^2 for x in Di])
	LL=[(PF/x^2).abs() for x in Di]
	LL.sort()
	r=len(M)
	return sum([(FC[i]-LL[i]).abs() for i in range(r)]) < ep


def ModularCriterionGeneral(M,ep):		# problem: very slow compared to the pseudo-unitary case
	if NonCo(M):
		return False
	if ModularCriterion(M,ep):
		return True
	FC=FormalCodegreesCoNum(M)
	FC.sort()
	r=len(M)
	Ch=CharacterTable(M)
	for i in range(r):
		Di=[Ch[j][i] for j in range(r)]
		if prod(Di).abs() > ep:
			dim=sum([x^2 for x in Di])
			LL=[(dim/x^2).abs() for x in Di]
			LL.sort()
			if sum([(FC[i]-LL[i]).abs() for i in range(r)]) < ep:
				return True
	return False	
	
def SortFusionData(M):
	#print(M)
	L=[matrix(m).norm() for m in M]
	sL=copy.deepcopy(L)
	sL.sort()
	r=len(L)
	P=[]
	C=[]
	for i in range(r):
		a=sL.index(L[i])
		C.append(a)
		if not a in P:
			P.append(a)
		else:
			c=0
			for x in C:
				if x==a:
					c+=1
			P.append(a+c-1)
	#print(P)
	return [[[M[P[i]][P[j]][P[k]] for k in range(r)] for j in range(r)] for i in range(r)]		

def BurciuModularType(L):
	dim=sum([x**2 for x in L])
	li=list(factor(dim))
	P=[l[0] for l in li]
	c=0
	for x in L:
		if x==1:
			c+=1
	li=list(factor(c))
	Q=[l[0] for l in li]
	for x in L:
		li=list(factor(x))
		for l in li:
			p=l[0]
			if not p in Q:
				Q.append(p)
	P.sort()
	Q.sort()
	return P==Q

def LagrangePointedType(L):
	dim=sum([x**2 for x in L])
	c=0
	for x in L:
		if x==1:
			c+=1
	return dim%c==0

def Burciu(M):
	r=len(M)
	if NonCo(M):
		#print('noncommutative, not computed')
		return True
	if not ExtendedCyclo(M):
		#print('non-cyclo, not computed')
		return True
	SR=SubRings(M)
	AChM = AlgCharacterTable(M)
	CC=[(sum([AChM[i][j]*(AChM[i][j].conjugate()) for i in range(r)])) for j in range(r)]
	c1=CC[0]
	for p in SR[1:-1]:
		CCp = [(sum([AChM[i][j]*(AChM[i][j].conjugate()) for i in p])) for j in range(r)]
		cp1=CCp[0]
		for j in range(r):
			#print([c1,CCp[j],cp1,CC[j]])
			x=UCF((c1*CCp[j])/(cp1*CC[j]))
			if '/' in list(str(x)):
				#print([p,j])
				return False
	return True

def Burnside(M):
	for m in M:
		mm=matrix(m)
		if mm.norm()>1 and mm.determinant()!=0:
			return False
	return True

'''
def ProdIdemp(M,p):	# make it much simpler, assuming commutative, just conside the eigenvalues of the product
	r=len(M)
	MM=[matrix(m) for m in M]
	dims=[MM[i].norm() for i in range(r)]
	pp=prod(dims)
	B=prod([MM[i]/dims[i] for i in range(r)])
	B2=B*B
	B4=B2*B2
	if p==1:
		c=(pp*(B[0]-B2[0])).norm()		# we do like that to avoid numerical zero which are formal nonzero (here 1/p is very close to zero)
		#print(pp*B[0],pp*B2[0])
	if p==2:
		c=(pp*pp*(B4[0]-B2[0])).norm()
		#print(c)
	return c < 0.000001			# need to rewrite with exact in the cyclo case, because caused trouble
'''
# new version:

def DualBurnside(M):#ProdIdemp(M):			# equivalent to dual-Burnside
	B=prod([matrix(m) for m in M]); #print((B^2)[0])
	E=B.eigenvalues()
	m=max(E)
	for ei in E:
		if ei!=0 and (ei-m).abs()>0.000001 and (ei+m).abs()>0.000001:  # warning, write with cyclo...
			return False
	return True 

def IsWeaklyIntegral(M):
	di=sum([matrix(x).norm()^2 for x in M])
	return (di-round(di)).abs() <= 0.0001


# code for the regular element of the adjoint subring

def RegAdjIdentity(M):		# dual-Burnside
	r=len(M)
	MM=[matrix(m) for m in M]
	S=sum([m*(m.transpose()) for m in MM])
	S1=S[0]
	S2=(S**2)[0]
	S3=(S**3)[0]
	A2=[]; A3=[]
	for i in range(r):
		if S2[i]!=0:
			A2.append(i)
		if S3[i]!=0:
			A3.append(i)
	if A2==A3:
		dims=[MM[i].norm() for i in range(r)]
		pp=prod(dims)
		dim=sum([dims[i]**2 for i in A2])
		B=prod([MM[i]/dims[i] for i in range(r)])
		B2=B**2
		P2=B2[0]
		R=[]
		for i in range(r):
			if i in A2:
				R.append(MM[i].norm()/dim)
			else:
				R.append(0)
		c=(pp*pp*(vector(R)-P2)).norm()
		#print(c)
		print(vector(R),P2)
		return c < 0.000001	# need to rewrite with exact in the cyclo case, because caused trouble
	else:
		print('extra iteration required')

def IsNil(M):
	r=len(M)
	MM=[matrix(m) for m in M]
	A=list(range(r))
	n=0
	B=M
	while n<r and len(B)>1:
		n+=1
		B=AdSub(B)
	return len(B)==1

def AdSub(M):
	A=[m[0].index(1) for m in M]
	r=len(A)
	S=((sum([matrix(m)*(matrix(m).transpose()) for m in M]))**r)[0]		# need a proof that **r is enough
	R=[]
	for i in range(r):
		if S[A[i]]!=0:
			R.append(M[i])
	return R

def Comut(M,N):
	r=len(M)
	A=[m[0].index(1) for m in N]
	X=[]
	for m in M:
		S=(matrix(m)*(matrix(m).transpose()))[0]
		c=0
		for i in range(r):
			if S[i]!=0 and not i in A:
				c=1
				break
		if c==0:
			X.append(m)
	BM=matrix(M[0])+sum([matrix(m) for m in X])
	SS=(BM**r)[0]
	B=[]
	for i in range(r):
		if SS[i]!=0:
			B.append(M[i])
	return B

#def Perp(M):
	

'''
GAP code for groups:
gap> for n in [2..1023] do if Size(Set(Factors(n)))=1 then Print([n]); N:=NrSmallGroups(n);; for m in [1..N] do g:=SmallGroup(n,m);; L:=CharacterDegrees(g);; irr:=Irr(g);; p:=Product(L, l->l[1]^l[2]);; P:=Product(irr)/p;; Q:=P^2;; if Q<>Q^2 then Print([n,m],Q); fi; od; fi; od;
'''

def BurciuFormula(M):
	r=len(M)
	MM=[matrix(m) for m in M]
	dims=[m.norm() for m in MM]
	D=sum([d^2 for d in dims])
	A=(1/D)*sum([dims[i]*MM[i] for i in range(r)])
	B=prod([MM[i]/dims[i] for i in range(r)])	
	c=(A-B).norm()
	return c < 0.0000001

def BurciuFormulExact(M):
	r=len(M)
	MM=[matrix(m) for m in M]
	dims=AlgDims(M)
	D=sum([d^2 for d in dims])
	A=(1/D)*sum([dims[i]*MM[i] for i in range(r)])
	B=prod([MM[i]/dims[i] for i in range(r)])	
	c=(A-B).norm()
	return c #< 0.0000001

def BurciuProperty(M): #with a zero entry in each column of its character table (except the first one)
	r=len(M)
	if NonCo(M):
		#print('noncommutative, not computed')
		return False
	else:
		Ch=CharacterTable(M)
		for j in range(1,r):
			if (prod([Ch[i][j] for i in range(r)])).n().abs() > 0.0000001:
				return False
	return True
	
def UnitaryCheckingAll(M):
	if not Axioms(M):
		return False
	if not NoSpectrumCriterion2(M):
		return False
	if not OneSpectrumCriterion2(M):
		return False
	if not PositiveCo(M,3):
		return False
	if not OstrikInequality(M):
		return False
	T=NonCo(M)
	if T:
		if not CycloFormalCodegrees(M):
			return False
	if not T:
		if not ExtendedCyclo(M):
			return False
	if not Lagrange(M):
		return False
	if not PseudoUnitaryDrinfeld(M):
		return False
	if not DnumberCrit(M):
		return False
	return True


def CheckingListUnitary(L,t):
	r=len(L)
	Slow=[]
	LU=[]
	for i in range(r):
		if i%100==0:
			print([i])
		M=L[i]
		def function():
			UnitaryCheckingAll(M)
		p1 = Process(target=function)
		p1.start()
		p1.join(t)
		if p1.is_alive():
			p1.terminate()
			Slow.append(M)
		elif UnitaryCheckingAll(M):
			LU.append(M)
			print(M)
	return [LU,Slow]




def PseudoUnitaryDrinfeld(M):
	LL=FormalCodegreesNC(M)
	if type(LL)==str:
		print(LL)
		return LL
	x=max(LL)
	for y in LL:
		yy=UCF(x/y)
		if '/' in list(str(yy)):
			return False
	return True

def PseudoUnitaryDrinfeldTime(M,t):
		def function():
			PseudoUnitaryDrinfeld(M)
		p1 = Process(target=function)
		p1.start()
		p1.join(t)
		if p1.is_alive():
			p1.terminate()
			return('too slow')
		else:
			return PseudoUnitaryDrinfeld(M)

def SphericalDrinfeld(M):
	r=len(M)
	ChAl=AlgCharacterTable(M)
	LL=[sum([ChAl[i][j]*(ChAl[i][j].conjugate()) for i in range(r)]) for j in range(r)]
	for j in range(r):		# Warning: here we reduce to column w/o zero and non-real entries for spherical
		c=0
		for i in range(r):
			if real_part(ChAl[i][j])==0:
				c=1
				break
		if c==0:
			cc=0
			x=LL[j]
			for y in LL:
				yy=UCF(x/y)
				if '/' in list(str(yy)):
					cc=1
					break
			if cc==0:
				return True
	return False

def PivotalDrinfeld(M):
	r=len(M)
	ChAl=AlgCharacterTable(M)
	LL=[sum([ChAl[i][j]*(ChAl[i][j].conjugate()) for i in range(r)]) for j in range(r)]
	for j in range(r):		# Warning: here we reduce to column w/o zero entries for pivotal.
		if prod([ChAl[i][j] for i in range(r)])!=0:	
			cc=0
			x=LL[j]
			for y in LL:
				yy=UCF(x/y)
				if '/' in list(str(yy)):
					cc=1
					break
			if cc==0:
				return True
	return False

def IsDnumber(x):
	p=list(UCF(x).minpoly())
	n=len(p)-1
	A=p[0]
	d=0
	for i in range(n+1):
		a=p[i]
		j=n-i
		y=UCF((a^n)/(A^j))
		if '/' in list(str(y)):
			d=1
			break
	return d==0

def DnumberCrit(M):
	if not ExtendedCyclo(M):
		return 'non-Extended-cyclo'
	L=FormalCodegreesDimE(M)
	for x in L:
		if not IsDnumber(x):
			return False
	return True

def DnumberCritTime(M,t):
	def function():
		DnumberCrit(M)
	p1 = Process(target=function)
	p1.start()
	p1.join(t)
	if p1.is_alive():
		p1.terminate()
		return('too slow')
	else:
		return DnumberCrit(M)
	
def NonCo(l):
	M=[matrix(m) for m in l]
	for A in M:
		for B in M:
			if A*B!=B*A:
				return True
	return False

def BasicCenter(M):		# generalize to non-basic element to get a Drinfeld-like center
	C=[]
	r=len(M)
	for i in range(r):
		c=0
		for j in range(r):
			if M[i][j] != M[j][i]:	
				c=1
				break
		if c==0:
			C.append(i)		
	return C

def IsCentral(M,l):
	r=len(M)
	for i in range(r):
		A=[sum([M[i][j][k] for j in l]) for k in range(r)]; B=[sum([M[j][i][k] for j in l]) for k in range(r)]
		if A!=B:
			print(A,B)
			return False
	return True					
				
def ExtendedCyclo(M):	
	for k in range(len(M)):
		N=matrix(QQ,M[k])
		f = N.minpoly()#; print(factor(f))
		K.<a> = f.splitting_field()#; print(f,K,K.conductor())
		deg=K.degree()
		r=f.degree()
		l=r%3; q=r//3
		if (l==0 and deg>3**q) or (l==1 and deg>4*3**(q-1)) or (l==2 and deg>2*3**q):	# Burns-Goldsmith theorem on maximal order abelian subgroup of Sn 
			return False
		elif not K.is_abelian():		
			return False
	return True


def Rational(M):	
	for k in range(len(M)):
		N=matrix(QQ,M[k])
		f = N.minpoly()#; print(factor(f))
		K.<a> = f.splitting_field()#; print(f,K,K.conductor())
		deg=K.degree()
		r=f.degree()
		l=r%3; q=r//3
		if (l==0 and deg>3**q) or (l==1 and deg>4*3**(q-1)) or (l==2 and deg>2*3**q):	# Burns-Goldsmith theorem on maximal order abelian subgroup of Sn 
			return False
		if not K.is_abelian():		
			return False
		if K.conductor()!=1:
			return False
	return True

def ExtendedCycloTime(M,t):
		def function():
			ExtendedCyclo(M)
		p1 = Process(target=function)
		p1.start()
		p1.join(t)
		if p1.is_alive():
			p1.terminate()
			return('too slow')
		else:
			return ExtendedCyclo(M)
	

def CycloFormalCodegrees(M):
	R=MatrixR(M)	
	f = R.minpoly()
	K.<a> = f.splitting_field()#; print(f,K,K.conductor())
	deg=K.degree()
	r=f.degree()
	l=r%3; q=r//3
	if (l==0 and deg>3**q) or (l==1 and deg>4*3**(q-1)) or (l==2 and deg>2*3**q):	# Burns-Goldsmith theorem on maximal order abelian subgroup of Sn 
		return False
	elif not K.is_abelian():		
		return False
	return True


'''
	for i in range(l):
		a=matrix(kk,M[i])
		ta=a.transpose()
		if not a*ta==ta*a:
			return 'Non-normal' # useless if M is "really" a commutative fusion ring (just a double-check) # transpose enough because the entries are real
		for j in range(i,l):
			b=matrix(kk,M[j])
			if not a*b==b*a:
				return 'Non-commutative'  # the notion of Character Table makes sense only for a commutative fusion ring (with normal -> simultaneously diagonalisable)
'''
	
def CharacterTable(M):
	if NonCo(M):
		print('noncommutative')
		return True
	l=len(M)
	r=len(M[0])
	kk=QQ.algebraic_closure()
	L=[matrix(QQ,M[j]) for j in range(l)]
	K,_,_ = number_field_elements_from_algebraics(sum([m.eigenvalues() for m in L], []), minimal=True)
	p = identity_matrix(K,r)
	q = ~p
	for i in range(l):
		a=q*L[i]*p
		da, pa = a.change_ring(K).jordan_form(transformation=True)
		p=p*pa
		q=~p
	sigma=K.embeddings(QQbar)[0]
	P=p.apply_map(sigma)
	Q=q.apply_map(sigma)
	P=matrix([[CIF(P[j][i]) for i in range(r)] for j in range(r)])
	Q=matrix([[CIF(Q[j][i]) for i in range(r)] for j in range(r)])
	L=[Q * L[j] * P for j in range(l)]
	if DimIrreps(L) !={1}:	 # useful to see the block structure			# important here, need update
		print('simultaneous diag problem')
		return 'simultaneous diag problem'
	Ch=[[L[i][j][j] for j in range(r)] for i in range(l)]
	CC=[(sum([Ch[i][j]*(Ch[i][j].conjugate()) for i in range(l)])).n() for j in range(r)]
	P=PermutSortReverse(CC)
	ChR=[[Ch[i][P[j]] for j in range(r)] for i in range(l)]
	return DimFirst(ChR)
	
def CommutativeCharacterTable(M,p):	# this code computes the commutative part of the character table (complete if the fusion ring )
	if p==0:			# it is the complete table if the ring is commutative. 
		F=QQ			# it solves the dimension equation, alternative method than function CharacterTable
	else:
		F=GF(p)	
	n=len(M)	
	R = PolynomialRing(F, n, 'd')
	dim = R.gens()
	Eq=[dim[i]*dim[j]-sum(M[i][j][k]*dim[k] for k in range(n)) for i in range(n) for j in range(n)]
	Eq.append(dim[0]-1)
	Id=R.ideal(Eq); G=Id.groebner_basis()
	FF=Id.variety(F.algebraic_closure())
	Ch=[[f[d] for d in dim] for f in FF]	
	Ch.sort(reverse=true)
	MC=matrix(Ch).transpose()
	return [list(m) for m in MC]	
		

def DimFirst(Ch):
	r=len(Ch)
	for j in range(r):
		L=[Ch[i][j] for i in range(r)]
		if sum([(abs(l-abs(l))).n(digits=14) for l in L])<0.0000000001:
			break
	if j==0:
		return Ch
	else:
		return [[Ch[i][Transp(jj,0,j)] for jj in range(r)] for i in range(r)]
		
def Transp(x,i,j):
	if x==i:
		return j
	if x==j:
		return i
	return x
	

def DimIrreps(M):
	r=len(M)
	N=[[[0 for k in range(r)] for j in range(r)] for i in range(r)]
	for i in range(r):
		for j in range(r):
			for k in range(r):	
				if abs((M[i][j][k]).n(digits=14))>0.0000000001:		#that needs to be improved
					N[i][j][k]=1
	SN=[[sum([N[i][j][k] for i in range(r)]) for j in range(r)] for k in range(r)]
	S=[[i] for i in range(r)]
	for i in range(r):
		for j in range(r):
			if SN[i][j]!=0:
				if not j in S[i]:
					S[i].append(j)
	SS=[]
	for s in S:
		s.sort()
		if not s in SS:
			SS.append(s)
	#print(SS)
	return {len(i) for i in SS}


def MatrixBlockFinder(M):
	r=len(M)
	N=[[0 for j in range(r)] for i in range(r)]
	for i in range(r):
		for j in range(r):
			if abs((M[i][j]).n(digits=14))>0.0000000001:
				N[i][j]=1
	S=[[i] for i in range(r)]
	for i in range(r):
		for j in range(r):
			if N[i][j]!=0:
				if not j in S[i]:
					S[i].append(j)
	SS=[]
	for s in S:
		s.sort()
		if not s in SS:
			SS.append(s)
	return SS
	

def PermutSortReverse(A):
	B=copy.deepcopy(A)
	B.sort()
	B.reverse()
	P=[]
	for b in B:
		for i in range(len(A)):
			if (not i in P) and (A[i]==b):
				P.append(i)
	return P

def SchurReformulated(M):		# maybe pb with new version of CharacterTable
	l=len(M)
	Ch=CharacterTable(M)
	if type(Ch)==str:
		print(Ch)
		return False	# it is not necessarily False, but Noncommutative, so not for the Commutative Schur Criterion
	else: 
		dim=[max(Ch[i]) for i in range(l)]
		for i in range(l):
			for j in range(i,l):
				for k in range(j,l):
					aa=sum([Ch[s][i]*Ch[s][j]*Ch[s][k]/max(Ch[s]) for s in range(l)])
					a=aa.n(digits=10)
					if abs(a)>0.00000001:
						if abs(imag_part(a))>0.00000001 or real_part(a)<-0.00000001:		# improved with exact in cyclo case.
							return False
	return True

# Positivity comultiplication criterion (better than NC Schur):

def PositiveCo(MM,n):		# relevant for n>=3 only (higher positivity of comultiplication)
	S=EigenQuon(MM,n)
	for s in S:
		if abs(s)>0.00000001:
			if abs(imag_part(s))>0.00000001 or real_part(s)<-0.00000001:		# improved with exact in cyclo case.
				#print(s)
				return False
	return True

def Quon(MM,n):
	r=len(MM)
	M=[matrix(m) for m in MM]
	dim=[m.norm() for m in M]
	NN=[matrix([1]) for i in range(r)]
	for i in range(n):
		NN=[NN[j].tensor_product(M[j]) for j in range(r)]
	N=sum(NN[i]/((M[i].norm())**(n-2)) for i in range(r))
	return N

def FS3Quon(MM):	#for now, only for trivial Frobenius-Schur indicator
	r=len(MM)
	M=[matrix(m) for m in MM]
	FS=[]
	for i in range(r):
		if MM[i][i][0]==1:
			FS.append(1)
		else:
			FS.append(0)
	dim=[m.norm() for m in M]
	NN=[matrix([1]) for i in range(r)]
	for i in range(3):
		NN=[NN[j].tensor_product(M[j]) for j in range(r)]
	N=sum(FS[i]*NN[i]/((M[i].norm())**2) for i in range(r))
	return N

def FS3PositiveCo(MM):
	N=FS3Quon(MM)
	S=N.eigenvalues()
	for s in S:
		if abs(s)>0.00000001:
			if abs(imag_part(s))>0.00000001 or real_part(s)<-0.00000001:		# improved with exact in cyclo case.
				#print(s)
				return False
	return True

def DetQuon(MM,n):
	N=Quon(MM,n)
	return N.determinant()

def TrQuon(MM,n):
	N=Quon(MM,n)
	return N.trace()

def EigenQuon(MM,n):
	N=Quon(MM,n)
	return N.eigenvalues()

def MatrixR(M):
	r=len(M)
	Mat=[matrix(QQ,M[i]) for i in range(r)]
	d=Duality(M)
	return sum(Mat[i]*Mat[d[i]] for i in range(r))

def OstrikInequality(M):			# note that this criterion works as well for NC case (see Ostrik paper, it is a pseudo-unitary criterion)
	R=MatrixR(M)
	#print(2*(R**(-2)).trace().n(),(1+1/R.norm()))
	return 2*(R**(-2)).trace()<=(1+1/R.norm()) 

def OstrikInequalityOld(M):		# this version is much slower.
	r=len(M)
	Mat=[matrix(M[i]) for i in range(r)]
	d=Duality(M)
	R=sum(Mat[i]*Mat[d[i]] for i in range(r))
	L=R.eigenvalues()
	L=[real_part(numerical_approx(l)) for l in L]
	m=max(L)
	s=(1+1/m)/2-sum(1/l**2 for l in L)
	return s>=0

def simpletest(MAT):
	M=[matrix(m) for m in MAT]
	r=len(M)
	for i in range(1,r):
		MM=sum([(M[i])**j for j in range(r)])
		for k in range(r):
			if MM[i][k]==0:				
				return False
	return True

def AlgCharacterTable(M):
	r=len(M)
	rr=len(M[0])
	if NonCo(M):
		return True
	if not ExtendedCyclo(M):
		print('non-cyclo, not computed')
		return True
	Ch=CharacterTable(M)	# improve the code in order to do not have to use CharacterTable.
	Al=[]
	for i in range(r):
		Mi=matrix(QQ,M[i])
		f=Mi.minpoly()
		ff=Mi.charpoly()
		K.<a> = f.splitting_field()
		n = K.conductor()
		LL=ff.roots(CyclotomicField(n))
		LLL=[UCF(l[0]) for l in LL]
		Al.extend(LLL)
	Al=list(set(Al))
	ChAl=[]
	for i in range(r):
		ChAli=[]
		for j in range(rr):
			x=Ch[i][j]
			for s in Al:
				#print([s,x])
				if abs(s.n()-x.n())<0.000001:		# to be improved with some better field
					ChAli.append(s)
					break
		ChAl.append(ChAli)
	return ChAl

def DualCoeff(M):
	r=len(M)
	ChAl=AlgCharacterTable(M)
	if ChAl in [True, False]:
		return 'not computed'
	CC=[sum([ChAl[i][j]*(ChAl[i][j].conjugate()) for i in range(r)]) for j in range(r)]
	Type=[ChAl[i][0] for i in range(r)]
	dim=CC[0]#; print('CC=',CC)
	return [[[UCF((dim/(CC[i]*CC[j]))*sum([ChAl[s][i]*ChAl[s][j]*((ChAl[s][k]).conjugate())/Type[s] for s in range(r)])) for k in range(r)] for j in range(r)] for i in range(r)]	#problem: need to take complex conjugate of ChAl[s][k]
	
def RationalDualCoeff(M):
	L=DualCoeff(M)
	if L=='not computed':
		return L
	for l in L:
		for ll in l:
			for lll in ll:
				if E in list(str(lll)):
					return False
	return True

def Isaacs(M,p,q,stro):		#### (p/q)-Isaacs
	r=len(M)
	ChAl=AlgCharacterTable(M)
	if ChAl in [True, False]:
		return ChAl
	CC=[sum([ChAl[i][j]*(ChAl[i][j].conjugate()) for i in range(r)]) for j in range(r)]
	Type=[ChAl[i][0] for i in range(r)]
	dim=CC[0]; print('CC=',CC)
	Coeff=[[[UCF((dim/(CC[i]*CC[j]))*sum([ChAl[s][i]*ChAl[s][j]*((ChAl[s][k]).conjugate())/Type[s] for s in range(r)])) for k in range(r)] for j in range(r)] for i in range(r)]	#problem: need to take complex conjugate of ChAl[s][k]
	for n in range(r**3):
		[i,j,k]=multibase(n,[r,r,r])
		cijk=Coeff[i][j][k]
		if '/' in list(str(cijk)):
			print('Non-integral coeff', [i,j,k], cijk)
			break
	#print('Class multiplication coefficients', Coeff)#; print([[[x.n() for x in y] for y in z] for z in Coeff])
	NZ=[prod([ChAl[i][j] for i in range(r)]) for j in range(r)]
	IZ=[]
	for k in range((r-1)*stro + 1):
		c=0
		if NZ[k]==0:
			print('Non-pivotal', 'Column=',k)
			IZ.append(-1)
		else:			# column w/o nonzero entries
			for i in range(r):
				if c==1:
					break
				for j in range(r):
					isa=UCF(((ChAl[i][j]*CC[k]/(ChAl[i][k]))**(q))/(CC[j])**(q-p))				#### (p/q)-Isaacs
					if '/' in list(str(isa)):
						c=1; print('Non-Isaacs', 'Column=',k, [i,j], [ChAl[i][j],CC[k],ChAl[i][k],CC[j]], isa)
						break
			IZ.append(c)
			#print(ChAl,Type,dim,CC)
			if c==0 and stro==1:
				cc=0
				for j1 in range(r):
					if cc==1:
						break
					for j2 in range(r):
						if cc==1:
							break
						for j3 in range(r):
							strong=UCF(sum([UCF(ChAl[i][j1])*UCF(ChAl[i][j2])*(UCF(ChAl[i][j3])*UCF(CC[k])/(UCF(ChAl[i][k])*UCF(CC[j3]))) for i in range(r)])**2/(UCF(CC[j1])*UCF(CC[j2])))
							if '/' in list(str(strong)):
								print([j1,j2,j3],strong)
								cc=1
								break
				if cc==1:
					print("Isaacs but not strongly", 'Colunm=',k,)
	print('Isaacs list = ', IZ)
	return IZ[0]==0 #pseudo-unitary case #Isaacs but not pseudo-unitary one: (0 in IZ) and (IZ[0]!=0) 

def FormalCodegreesConductor(M): 	# must be cyclo
	if not ExtendedCyclo(M):
		return 'non-extended-cyclo'
	r=len(M)
	d=Duality(M)
	R=sum([matrix(QQ,M[i])*matrix(QQ,M[d[i]]) for i in range(r)])#; print([[R[i][j] for j in range(r)] for i in range(r)])
	f=R.minpoly()
	K.<a> = f.splitting_field()
	return K.conductor()

def ConductorCriterion(M): 	# must be cyclo	# the (cyclotomic) conductor of the formal codegrees must divide the one of the type.
	c=FormalCodegreesConductor(M)
	if c=='non-extended-cyclo':
		return 'non-extended-cyclo'
	E=[ConductorDim(matrix(m)) for m in M] #; print(E)
	cc=1
	for x in E:
		cc=lcm(x,cc)
	#print(cc,c)	
	return cc%c==0

'''
sage: for i in range(16):
....:     for j in range(len(L[i])):
....:         M=L[i][j]
....:         c=ConductorCriterion(M)
....:         if c!='non-extended-cyclo':
....:             if not c:
....:                 print(AlgDims(M),M)

'''

def ConductorDim(m):	# matrix m must have minpoly with cyclotomic splitting field
	f=m.minpoly()
	L=list(f.factor())
	d=m.norm()
	for l in L:
		g=l[0]
		if g(d).abs()<0.000000001:		# should be improved
			K.<a> = g.splitting_field()
			return K.conductor()

def preFormalCodegrees(M):
	if not ExtendedCyclo(M):
		return 'non-extended-cyclo'
	r=len(M)
	d=Duality(M)
	R=sum([matrix(QQ,M[i])*matrix(QQ,M[d[i]]) for i in range(r)])#; print([[R[i][j] for j in range(r)] for i in range(r)])
	f=R.minpoly()
	ff=R.charpoly()
	K.<a> = f.splitting_field()
	n = K.conductor()
	return ff.roots(CyclotomicField(n))

def FormalCodegreesCoNum(M):
	r=len(M)
	R=sum([matrix(m)*(matrix(m).transpose()) for m in M])
	L=R.eigenvalues()
	return [x.abs() for x in L]
	
def MultGrp(l):
	ll=list(set(l))
	ll.sort()
	return [[i,l.count(i)] for i in ll]
	
def RevMultGrp(T):
	L=[]
	for l in T:
		L.extend([l[0] for i in range(l[1])])
	return L	

def IntFormalCodegrees(M):
	r=len(M)
	R=sum([matrix(m)*(matrix(m).transpose()) for m in M])
	f=R.charpoly()
	R.<x> = ZZ['x']
	P = R(f)
	roots = P.roots(multiplicities=True)
	ro=[]
	for l in roots:
		ro.extend([l[0] for i in range(l[1])])
	ro.sort()
	if not len(ro)==r:
		if NonCo(M):
			return [False, 'NonCommutative'+str(ro)]
		return [False, ro]	
	if NonCo(M):			# work in general for formal codegree NC case rank <=8, otherwise require hand
		T=MultGrp(ro)
		cc=0
		for t in T:
			if t[1]>=4:
				cc+=1
				t0=t
			else:	# if t[1] < 4 then it cannot from an irreducible of dim>1 since 2^2=4 (see Ostrik rank 3 paper)
				if ro[-1]%t[0]!=0:
					return [False,'NonCommutative'+str(ro)]			
		if cc>=2 or r>=10:
			return [True,'NonCommutativeHand'+str(ro)]		
		else:
			index=T.index(t0)		# ok t0 because cc<=1, in fact cc must be 1, otherwise cannot exclude (update)
			T[index]=[t0[0],t0[1]-4]
			ro=RevMultGrp(T)
			ro.append(t0[0]/2)
			ro.sort()
			if not t0[0]%2==0:
				return [False,'NonCommutative'+str(ro)]
			c=0
			for n in ro:
				if not ro[-1]%n==0:
					c=1
					break
			return [c==0,'NonCommutative'+str(ro)]					
	c=0
	for n in ro:
		if not ro[-1]%n==0:
			c=1
			break			
	return [c==0,ro]

def IsIntDrinfeldInter(M,v,ro):
	if not v:
		return False
	else:	
		if type(ro)==str:
			print(ro)
			return True
		FPdim=max(ro); #print(FPdim, ro)
		for n in ro:
			if not FPdim%n==0:
				return False
	return True

def IsIntDrinfeld(M):
	[v,ro]=IntFormalCodegrees(M)
	return IsIntDrinfeldInter(M,v,ro)						

def FolderChecking():
	L = []
	c = 0
	# Regular expression to match the filename pattern
	pattern = re.compile(r'(\[.*?\])(\[.*?\])\.fus')

	# Get the list of all .fus files in the current directory
	for filename in os.listdir('.'):
		if filename.endswith('.fus'):
			match = pattern.match(filename)
			if match:
				# Extract and convert the lists from the filename
				list1_str, list2_str = match.groups()
				dims = eval(list1_str)
				FPdim=sum([i**2 for i in dims])
				d = eval(list2_str)
				#print(dims,d)
				with open(filename) as f:
					for line in f:
						M = eval(line)
						[v,ro]=IntFormalCodegrees(M)		
						if v and IsIntDrinfeldInter(M,v,ro):	# second part new, redundent? (double check AlekseyevBrunsDongPalcoux)
							L.append([FPdim,dims,d,ro,M])
	L.sort(key=lambda x: (x[0], x[1], x[2]))	# to avoid sorting problem with noncommutative					
	return L
	
def FolderCheckingAll():
	L=[]
	for filename in os.listdir('.'):
		if filename.endswith('.fus'):
			with open(filename) as f:
				for line in f:
					M = eval(line)	
					L.append(M)			
	return L	

def FolderSimple():
	L = []
	c = 0
	# Regular expression to match the filename pattern
	pattern = re.compile(r'(\[.*?\])(\[.*?\])\.fus')

	# Get the list of all .fus files in the current directory
	for filename in os.listdir('.'):
		if filename.endswith('.fus'):
			match = pattern.match(filename)
			if match:
				# Extract and convert the lists from the filename
				list1_str, list2_str = match.groups()
				dims = eval(list1_str)
				FPdim=sum([i**2 for i in dims])
				d = eval(list2_str)
				#print(dims,d)
				with open(filename) as f:
					for line in f:
						M = eval(line)
						if simpletest(M):
							L.append(M)
	return L		
	
def FolderNonCo():
	L = []
	c = 0
	# Regular expression to match the filename pattern
	pattern = re.compile(r'(\[.*?\])(\[.*?\])\.fus')

	# Get the list of all .fus files in the current directory
	for filename in os.listdir('.'):
		if filename.endswith('.fus'):
			match = pattern.match(filename)
			if match:
				# Extract and convert the lists from the filename
				list1_str, list2_str = match.groups()
				dims = eval(list1_str)
				FPdim=sum([i**2 for i in dims])
				d = eval(list2_str)
				#print(dims,d)
				with open(filename) as f:
					for line in f:
						M = eval(line)
						if NonCo(M):
							L.append(M)
	return L									

''' 
simple commutative non-pointed with non-perfect dual?
sage: for l in DSL:
....:     for M in l:
....:         if simpletest(M) and not NonCo(M):
....:             L=FormalCodegreesCoNum(M)
....:             L.sort()
....:             if len(L)>=2 and (L[-1]-L[-2]).abs()<0.000001 and (L[-1]-L[0]).abs()>0.000001:
....:                 print(M)

'''

def FormalCodegreesMult(M):
	L=preFormalCodegrees(M)
	if type(L)==str:
		return L
	return [l[1] for l in L]

def FormalCodegreesDimE(M):
	L=preFormalCodegrees(M)
	if type(L)==str:
		return L
	return [UCF(l[0]) for l in L]


def FormalCodegreesTable(M):
	r=len(M)
	ChAl=AlgCharacterTable(M)
	#if ChAl in [True, False]:
	#	return ChAl
	return [sum([ChAl[i][j]*(ChAl[i][j].conjugate()) for i in range(r)]) for j in range(r)]

def FormalCodegreesNC(M):		# designed for NC case of rank<10
	r=len(M)
	if not NonCo(M):
		return FormalCodegreesDimE(M)
	elif r>9:
		return 'rank should be at most 9'
	else:
		L=preFormalCodegrees(M)
		FPdim=sum([matrix(m).norm()**2 for m in M])
		if type(L)==str:
			return L
		Mu=[l[1] for l in L]
		c=0; d=0
		for i in range(len(Mu)):
			if Mu[i]>=4:
				if abs(FPdim.n()-L[i][0].n())>0.00001:	# slight improvment to avoid some ambiguity
					c+=1
					ii=i
				else:
					d+=1		# in case of two f_E dim(E) = FPdim, very specific to small rank..., otherwise, definitely need a better code (simultaneous block diagonalization)
					iii=i
		if d==2 or (d==1 and len(L)==1):
			ii=iii
		elif c==0 or c>1:
			return 'ambiguity, need a better code'
		F=[UCF(l[0]) for l in L[:ii]]
		F.append(L[ii][0]/2)
		if Mu[ii]>4:
			F.append(L[ii][0])
		F.extend([UCF(l[0]) for l in L[ii+1:]])
		return F

def AlgDims(M):		# need to check extended cyclo
	r=len(M)
	E=[]
	for i in range(r):
		N=matrix(QQ,M[i])
		f=N.minpoly()
		K.<a> = f.splitting_field()
		n = K.conductor()
		LL=f.roots(CyclotomicField(n))
		LLL=[UCF(l[0]) for l in LL]
		RL=[]
		for a in LLL:
			if a.imag_part()==0:
				RL.append(a)
		E.append(max(RL))
	return E
	
def Dims(M):		
	MM=[matrix(m) for m in M]
	return [m.norm() for m in MM]

def FrobeniusType(M,pp,qq):	#only in the cyclo case
	E=AlgDims(M)
	dim=sum([a**2 for a in E])
	#print('FPdim = ',dim)
	#print('FPdims = ',E)
	for a in E:
		q=UCF((dim^pp)/(a^qq))
		if '/' in list(str(q)):
			#print(q)
			return False
	return True

def Lagrange(M):		# need to check extended cyclo (warning: Lagrange is stronger, so for classification, may need to check Lagrange for non-ExtnededCyclo by hand)
	E=AlgDims(M)
	SL=SubRings(M)
	dim=sum([a**2 for a in E])
	for l in SL:
		diml=sum([E[i]**2 for i in l])
		q=UCF(dim/diml)
		if '/' in list(str(q)):
			return False
	return True

def LagrangeType(M,L):	# here the type L must be cyclo, but not necessarily M ExtendedCyclo as required above (again, for non-cyclo type, Lagrange should be checked by hand)
	SL=SubRings(M)
	dim=sum([a**2 for a in L])
	for l in SL:
		diml=sum([L[i]**2 for i in l])
		q=UCF(dim/diml)
		if '/' in list(str(q)):
			return False
	return True
	

def Dual(S):
	l=len(S)
	L=[]
	for i in range(l):
		for j in range(l):
			if S[i][j][0]==1:
				L.append(j)
	return L

def BinomialList(L,n):
	global LL,m
	m=n
	LL=[]
	BinomialListInter(L,[])
	LL.sort()
	return LL

def BinomialListInter(L,T):
	global LL,m
	l=len(L)
	t=len(T)
	if t==m:
		TT=copy.deepcopy(T)
		TT.sort()
		LL.append(TT)
	elif t<m:
		for i in range(l):
			TT=copy.deepcopy(T)
			TT.append(L[i])
			BinomialListInter(L[:i],TT)

def SubRings(M):
	BL=[]
	r=len(M)
	d=Duality(M)
	L=list(range(1,r))
	for n in range(r):
		LL=BinomialList(L,n)
		for ll in LL:
			l=[0]
			l.extend(ll)
			c=0
			for i in l:
				if not d[i] in l:
					c=1
					break
			if c==0:
				for i in l:
					for j in l:
						for k in range(r):
							if M[i][j][k]!=0 and not k in l:
								c=1
								break
						if c==1:
							break
					if c==1:
						break
				if c==0:
					BL.append(l)
	return BL


def SubRingMatrix(M,p):
	return [[[M[i][j][k] for k in p] for j in p] for i in p]
						

def NoSpectrumCriterion2(M):
	#cdef int r,i1,i2,i3,i4,i5,i6,i7,i8,i9,k
	#cdef list d
	d=Dual(M)
	r=len(M)
	for i4 in range(r):
		for i1 in range(r):
			for i6 in range(r):
				if M[i4][i1][i6]!=0:
					for i2 in range(r):
						for i5 in range(r):
							if M[i5][i4][i2]!=0:
								for i3 in range(r):
									if M[i2][i1][i3]==1 and M[i5][i6][i3]!=0 and (sum([M[d[i5]][i2][k]*M[i6][d[i1]][k] for k in range(r)])==1 or sum([M[i2][d[i4]][k]*M[i3][d[i6]][k] for k in range(r)])==1 or sum([M[i5][i4][k]*M[i3][d[i1]][k] for k in range(r)])==1):
										for i9 in range(r):
											for i7 in range(r):
												if M[i7][i9][i1]!=0:
													for i8 in range(r):
														if M[i2][i7][i8]!=0 and M[i8][i9][i3]!=0 and (sum([M[d[i2]][i8][k]*M[i1][d[i9]][k] for k in range(r)])==1 or sum([M[i2][i7][k]*M[i3][d[i9]][k] for k in range(r)])==1 or sum([M[i8][d[i7]][k]*M[i3][d[i1]][k] for k in range(r)])==1) and sum([M[i4][i7][k]*M[d[i5]][i8][k]*M[i6][d[i9]][k] for k in range(r)])==0:
															#print([i1,i2,i3,i4,i5,i6,i7,i8,i9])
															return False
	return True
	
def OneSpectrumCriterion2(M):
	#cdef int r,i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,k
	#cdef list d
	d=Dual(M)
	r=len(M)
	for i0 in range(r):
		for i4 in range(r):
			for i7 in range(r):
				if M[i4][i7][i0]==1:
					for i5 in range(r):
						for i8 in range(r):
							if M[d[i5]][i8][i0]==1:
								for i2 in range(r):
									if M[i5][i4][i2]!=0 and M[i2][i7][i8]!=0 and (sum([M[i5][i4][k]*M[i8][d[i7]][k] for k in range(r)])==1 or sum([M[i2][d[i4]][k]*M[i8][d[i0]][k] for k in range(r)])==1 or sum([M[d[i5]][i2][k]*M[i0][d[i7]][k] for k in range(r)])==1):
										for i9 in range(r):
											for i6 in range(r):
												if M[i6][d[i9]][i0]==1 and sum([M[i4][i7][k]*M[d[i5]][i8][k]*M[i6][d[i9]][k] for k in range(r)])==1:
													for i1 in range(r):
														if M[i4][i1][i6]!=0 and M[i7][i9][i1]!=0 and (sum([M[i4][i7][k]*M[i6][d[i9]][k] for k in range(r)])==1 or sum([M[i0][d[i7]][k]*M[i6][d[i1]][k] for k in range(r)])==1 or sum([M[d[i4]][i0][k]*M[i1][d[i9]][k] for k in range(r)])==1):
															for i3 in range(r):
																if M[i2][i1][i3]==0 and M[i5][i6][i3]!=0 and M[i8][i9][i3]!=0 and (sum([M[i5][i0][k]*M[i3][d[i9]][k] for k in range(r)])==1 or sum([M[i8][d[i0]][k]*M[i3][d[i6]][k] for k in range(r)])==1 or sum([M[d[i5]][i8][k]*M[i6][d[i9]][k] for k in range(r)])==1):
																	#print([i0,i1,i2,i3,i4,i5,i6,i7,i8,i9])
																	return False
	return True

def Mult(M):
	r=len(M)
	return max([max([max(M[i][j]) for j in range(r)]) for i in range(r)])

def ListTable(L,rr,m):
	T=[[0 for i in range(m)] for j in range(rr)]
	for M in L:
		r=len(M)
		m=Mult(M)
		T[r-1][m-1]+=1
	return T

def Nonzero(l):
	c=0
	for ll in l:
		if ll!=0:
			c+=1
	return c

def Hadamard(L):
	BL=[]; FL=[]
	for LL in L:
		for M in LL:
			d=Duality(M)
			r=len(M)
			for i in range(1,r):
				mm=M[i]
				ii=d[i]
				l=mm[ii]
				T=[]
				for j in range(1,len(l)):
					t=l[j]
					if t!=0:
						T.append(j)
				k=-1
				if len(T)==2 and i in T:
					T.remove(i)
					k=T[0]
				if len(T)==1 and (not i in T):
					k=T[0]
				if k!=-1:
					if not M in FL:
						FL.append(M)
					kk=d[k]
					[s,l,t,m]=[M[i][ii][i],M[i][ii][k],M[k][kk][i],M[k][kk][k]]
					A=matrix(M[i]); a=A.norm(); b=matrix(M[k]).norm()
					if ii==i:
						x=((s*s*t)/a + (l*l*m)/b + 1)*((s*t*t)/a + (l*m*m)/b + 1)-((l*l*l)/a + (t*t*t)/b)**2
					if ii!=i:
						ta3=((A*A)[i][0])
						x=(2*s*s*s)/a + 1 - (s*ta3)*(s+ta3)/a
					if x<0:
						if not M in BL:
							BL.append(M)
							print([i,k])
							print([s,l,t,m])
							print(M)
							print(PositiveCo(M,3))
	print('total = ', len(FL))
	print('ruled out = ', len(BL))
	
	
### ExtendedCommutativeIntegralDrinfeld ###

def ListToType(L):
	T=[[1,1]]
	t=1
	n=0
	for i in L[1:]:
		if i==t:
			n+=1
		else:
			if n!=0:
				T.append([t,n])
			t=i
			n=1
	T.append([t,n])
	return T

def find_partitions(A, B, n, current_list=[], position=0, current_sum=0):
    # Base case: if we've reached the end of the list
    if position == len(A):
        # Check if the current_sum equals n and return the current list if true
        if current_sum == n:
            yield list(current_list)  # Yield the current partition
        return

    # Iterate over all possible values for L[position] given the constraints
    for value in range(B[position] + 1):
        # Calculate new sum with the current value
        new_sum = current_sum + value * A[position]
        
        # If the new sum exceeds n, break the loop as further values will only increase the sum
        if new_sum > n:
            break
        
        # Append the current value to the list and move to the next position
        yield from find_partitions(A, B, n, current_list + [value], position + 1, new_sum)

def get_partitions(A, B, n):
    #
    # Validate input
    #if len(A) != len(B):
    #    raise ValueError("Lists A and B must have the same length")
    #if any(type(x) is not int or x <= 0 for x in A+B+[n]):
    #    raise ValueError("All inputs must be positive integers")
    #	
    # Generate and return all valid partitions
    return list(find_partitions(A, B, n))
'''
# Example usage
A = [2, 3, 5]
B = [3, 2, 1]
n = 10

partitions = get_partitions(A, B, n)
print("Partitions:", partitions)
'''

def is_valid_partial(A, LL, L, s, B):
    """
    Check if the partial solution is valid by ensuring the partial sums do not exceed B.
    """
    #print(L)
    for j in range(len(B)):
        partial_sum = sum(LL[i][L[i]][j] for i in range(s)); #print(j,partial_sum,B[j])
        if partial_sum > B[j]:
            return False
    return True

def find_solutions(A, B, LL, mu, L=[], position=0):
    """
    Recursively find all solutions that satisfy the condition, with early pruning.
    """
    l = len(A)
    ll= len(LL)
    if position == ll:  # If L is complete
        if all(B[j] == sum(LL[i][L[i]][j] for i in range(ll)) for j in range(l)):
            print('solution', L)
            yield list(L)
        return

    # Iterate over possible values for L[position]
    if position in mu:	# to avoid equivalent solutions
    	st=0
    else:
    	st=L[-1]	
    for value in range(st,len(LL[position])): 
        new_L = L + [value]
        if is_valid_partial(A, LL, new_L, position + 1, B):
            yield from find_solutions(A, B, LL, mu,new_L, position + 1)
        else:
            # Early pruning
            continue

def get_solutions(A, B, LL,mu):
    """
    Validates input and initiates the search for solutions.

    if not all(len(sublist) == len(A) for sublist in LL) or len(A) != len(B):
        raise ValueError("Invalid input sizes.")
    if any(not isinstance(sublist, list) or any(type(x) is not int or x <= 0 for sublist2 in sublist for x in sublist2) for sublist in LL):
        raise ValueError("All inputs must contain positive integers.")
    """
    return list(find_solutions(A, B, LL,mu))
'''
# Example usage
A = [1, 2]
B = [5, 8]
LL = [[[1, 2], [2, 1]], [[2, 3], [3, 2]]]  # Format: LL[i][j][k]

solutions = get_solutions(A, B, LL)
print("Solutions:", solutions)
'''


def ExtendedCommutativeIntegralDrinfeld(M):	# Extended to NC	# Observation a Grothendieck ring usually have a lot of solutions (relatively to rank and FPdim) whereas the non-Grothendieck sometimes few  
	if NonCo(M):							# find an exclusion by this criterion (passing the first two if, of course...)
		return 'noncommutative'
	if ExtendedCyclo(M) and ConductorCriterion(M) and PseudoUnitaryDrinfeld(M):	
		r=len(M)
		pFC=preFormalCodegrees(M)
		FC=[list(l) for l in pFC]
		Dims = AlgDims(M)
		T=ListToType(Dims)
		Dim = sum([i^2 for i in Dims])
		FD = [[Dim/l[0] - 1,l[1]] for l in FC]	# warning: -1 is because we can directly remove the unit as we deal with I(1)
		FD.sort()
		d=Duality(M)
		A=[sum([M[j][d[j]][i] for j in range(r)]) for i in range(r)]
		B=[]
		c=1
		for l in T[1:]:
			a=sum([A[c+i] for i in range(l[1])])
			c+=l[1]
			B.append(a)
		A = [l[0] for l in T[1:]]
		TT=FD[1:]; #print(TT)
		LL=[]
		for l in TT:
			GT=get_partitions(A, B, l[0])
			for i in range(l[1]):
				LL.append(GT)
		mmu=[l[1] for l in TT]	
		mu=[sum([mmu[i] for i in range(j)]) for j in range(len(mmu))]	
		print(A,B,LL)		
		LLL=get_solutions(eval(str(A)), eval(str(B)), eval(str(LL)),eval(str(mu)))		
		return [[LL[i][L[i]] for i in range(len(L))] for L in LLL]
			

'''
List of solutions for F210 (each list of integers should start by 1, omited here). Add a paragraph with explanations, some of these solutions, Morrison-Walker and spread open problem since 10 years

[[[1, 4, 0], [3, 0, 2], [3, 0, 2], [0, 1, 4], [4, 0, 3], [4, 0, 3]],
 [[1, 4, 0], [3, 0, 2], [3, 0, 2], [4, 0, 2], [0, 1, 5], [4, 0, 3]],
 [[2, 2, 1], [2, 2, 1], [3, 0, 2], [0, 1, 4], [4, 0, 3], [4, 0, 3]],
 [[2, 2, 1], [2, 2, 1], [3, 0, 2], [4, 0, 2], [0, 1, 5], [4, 0, 3]],
 [[2, 2, 1], [3, 0, 2], [3, 0, 2], [0, 1, 4], [0, 1, 5], [7, 1, 0]],
 [[2, 2, 1], [3, 0, 2], [3, 0, 2], [0, 1, 4], [3, 2, 2], [4, 0, 3]],
 [[2, 2, 1], [3, 0, 2], [3, 0, 2], [3, 2, 1], [0, 1, 5], [4, 0, 3]],
 [[2, 2, 1], [3, 0, 2], [3, 0, 2], [4, 0, 2], [0, 1, 5], [3, 2, 2]],
 [[3, 0, 2], [3, 0, 2], [3, 0, 2], [0, 1, 4], [2, 4, 1], [4, 0, 3]],
 [[3, 0, 2], [3, 0, 2], [3, 0, 2], [0, 1, 4], [3, 2, 2], [3, 2, 2]],
 [[3, 0, 2], [3, 0, 2], [3, 0, 2], [2, 4, 0], [0, 1, 5], [4, 0, 3]],
 [[3, 0, 2], [3, 0, 2], [3, 0, 2], [3, 2, 1], [0, 1, 5], [3, 2, 2]],
 [[3, 0, 2], [3, 0, 2], [3, 0, 2], [4, 0, 2], [0, 1, 5], [2, 4, 1]]]

What next?
Find ways to reduce this list to empty?
Or consider I(X), as above come from I(1)...?

'''				
	

################# old codes #################

'''
	N=zero_matrix(QQ,r)
	for i in range(r):
		Mi=matrix(QQ,M[i])
		Ti=Mi.transpose()
		Ni=Mi*Ti
		N+=Ni
	f = N.minpoly()
	ff=N.charpoly()
	K.<a> = f.splitting_field()
	n = K.conductor()
	L=ff.roots(CyclotomicField(n)); print('Formal Codegrees = ', [[l[0].n().real_part(),l[1]] for l in L], [[UCF(l[0]),l[1]] for l in L])
	LL=[UCF(l[0]) for l in L]
	rL=[l[0].n() for l in L]
	mm=max(rL)
	for ii in range(len(L)):
			if mm==rL[ii]:
				dim=LL[ii]
				break
'''

'''
	for x in LL:
		if not IsDnumber(x):
			print('non-d-number')	# d-number criterion
			break			

		p=list(UCF(x).minpoly())
		n=len(p)-1
		A=p[0]
		d=0
		for i in range(n+1):
			a=p[i]
			j=n-i
			y=UCF((a^n)/(A^j))
			if '/' in list(str(y)):
				d=1
				break
		if d==1:
			print('non-d-number')	# d-number criterion
			break

'''
