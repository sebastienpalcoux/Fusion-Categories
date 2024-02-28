
# %attach Nutstore/1/SAGE/ModularData.sage
UCF=UniversalCyclotomicField()
import copy

# Here the fusion rings must be commutative and cyclo.


def CharacterTable(M):
	l=len(M)
	kk=QQ.algebraic_closure()
	L=[matrix(QQ,M[j]) for j in range(l)]
	K,_,_ = number_field_elements_from_algebraics(sum([m.eigenvalues() for m in L], []), minimal=True)
	p = identity_matrix(K,l)
	q = ~p
	for i in range(1,l):
		a=q*L[i]*p
		da, pa = a.change_ring(K).jordan_form(transformation=True)
		p=p*pa
		q=~p
	sigma=K.embeddings(QQbar)[0]
	P=p.apply_map(sigma)
	Q=q.apply_map(sigma)
	P=matrix([[CIF(P[j][i]) for i in range(l)] for j in range(l)])
	Q=matrix([[CIF(Q[j][i]) for i in range(l)] for j in range(l)])
	L=[Q * L[j] * P for j in range(l)]
	Ch=[[L[i][j][j] for j in range(l)] for i in range(l)]
	CC=[(sum([Ch[i][j]*(Ch[i][j].conjugate()) for i in range(l)])).n() for j in range(l)]
	P=PermutSortReverse(CC)
	ChR=[[Ch[i][P[j]] for j in range(l)] for i in range(l)]
	return DimFirst(ChR)

def DimFirst(Ch):
	r=len(Ch)
	for j in range(r):
		L=[Ch[i][j] for i in range(r)]
		if sum([(abs(l-abs(l))).n() for l in L])<0.0000000001:
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

def Duality(S):
	l=len(S)
	L=[]
	for i in range(l):
		for j in range(l):
			if S[i][j][0]==1:
				L.append(j)
	return L

def AlgDim(M): # use only for commutative cyclo
	r=len(M)
	d=Duality(M)
	R=sum([matrix(QQ,M[i])*matrix(QQ,M[d[i]]) for i in range(r)])#; print([[R[i][j] for j in range(r)] for i in range(r)])
	f=R.minpoly()
	K.<a> = f.splitting_field()
	n = K.conductor()
	L=f.roots(CyclotomicField(n))
	LL=[UCF(l[0]) for l in L]
	return max(LL)

def AlgCharacterTable(M): # use only in the commutative cyclo case
	r=len(M)
	rr=len(M[0])
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

def FormalCodegrees(M):
	r=len(M)
	d=Duality(M)
	R=sum([matrix(QQ,M[i])*matrix(QQ,M[d[i]]) for i in range(r)])#; print([[R[i][j] for j in range(r)] for i in range(r)])
	f=R.minpoly()
	ff=R.charpoly()
	K.<a> = f.splitting_field()
	n = K.conductor(); print(n,f)
	L=ff.roots(CyclotomicField(n))
	LL=[]
	for l in L:
		LL.extend([UCF(l[0]) for i in range(l[1])])
	LL.sort()
	LL.reverse()
	return LL

def ListToType(L):	#made for usual type of fusion ring starting as [1,...]
	T0=[[1,1]]
	T=DirectListToType(L[1:])
	T0.extend(T)
	return T0
	
def DirectListToType(L):		# made for sorted list
	T=[]
	for l in L:
		if T!=[] and l==T[-1][0]:
			T[-1][1]+=1
		else:
			T.append([l,1])
	return T	

def NonCo(l):
	M=[matrix(m) for m in l]
	for A in M:
		for B in M:
			if A*B!=B*A:
				return True
	return False	

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
	
def preSmatrix(MZ):		# work for cyclo case only AND sorted.
	M=SortFusionData(MZ)
	BL=[]
	r=len(M)
	ACh=AlgCharacterTable(M)
	CC=[sum([ACh[i][j]*(ACh[i][j].conjugate()) for i in range(r)]) for j in range(r)]; #print(CC) #Much quicker than FormalCodegrees(M)
	dim=[ACh[i][0] for i in range(r)]; print([x.n() for x in dim])
	CCC=[CC[0]/CC[i] for i in range(r)]
	dim2=[dim[i]**2 for i in range(r)]
	CCC.sort()				
	dim2.sort()		# It was not sorted in previous version, a problem?? it was ordered by type order, ok in ABPP paper, but for Gert dataset, type not sorted.
	if not CCC==dim2:
			print(dim2,CCC)
			return [False]
	T=ListToType(CC); #print(T)
	TP=TypePerms(T)
	NCh=[[dim[j]*ACh[i][j] for j in range(r)] for i in range(r)]
	ltp=len(TP)
	for i in range(ltp):
		#print(i,ltp)
		P=TP[i]
		Ch=[[NCh[ii][P[j]] for j in range(r)] for ii in range(r)]
		MCh=matrix(Ch)
		if MCh==MCh.transpose():
			BL.append(Ch)
	return [len(BL)>0,BL]
	
	
def FormalCodegreesCoNum(M):
	r=len(M)
	R=sum([matrix(m)*(matrix(m).transpose()) for m in M])
	L=R.eigenvalues()
	return [x.abs() for x in L]	

	
# the following function is very efficient, it checks whether c1/cj = dj^2 for all j, where (di), (ci) are FPdims and formal codegrees.
	
def ModularCriterion(M,ep):		# M is assumed commutative and integral (to get pseudo-unitary)
	FC=FormalCodegreesCoNum(M)
	FC.sort()
	Di=[matrix(m).norm() for m in M]
	PF=sum([x^2 for x in Di])
	LL=[(PF/x^2).abs() for x in Di]
	LL.sort()
	r=len(M)
	return sum([(FC[i]-LL[i]).abs() for i in range(r)]) < ep	

def SelfTransposable(M): # only for commutative cyclo fusion rings # maybe quicker to do it numerically, replacing == by .abs().n()<0.0000001
	BL=[]
	r=len(M)
	ACh=AlgCharacterTable(M)
	CC=[sum([ACh[i][j]*(ACh[i][j].conjugate()) for i in range(r)]) for j in range(r)]
	dim=[ACh[i][0] for i in range(r)]
	CCC=[CC[0]/CC[i] for i in range(r)]
	dim2=[dim[i]**2 for i in range(r)]
	if not CCC==dim2:
			return False
	T=ListToType(CC)
	TP=TypePerms(T)
	NCh=[[dim[j]*ACh[i][j] for j in range(r)] for i in range(r)]
	ltp=len(TP)
	for i in range(ltp):
		P=TP[i]
		Ch=[[NCh[ii][P[j]] for j in range(r)] for ii in range(r)]
		MCh=matrix(Ch)
		if MCh==MCh.transpose():
			print(M); print(Ch)
			return True
	return False


def TypePerms(T):		# what about merging SelfTransposable with TypePerms?
	l=len(T)
	rT=[t[1] for t in T]
	sT=[sum(rT[:i]) for i in range(l)]
	TG=[SymmetricGroup(i) for i in rT]
	LTG=[len(G) for G in TG]
	N=prod(LTG)
	BL=[]
	for i in range(N):
		L=multibase(i,LTG)
		gL=[TG[j][L[j]] for j in range(l)]
		Z=[]
		for j in range(l):
			g=gL[j]
			s=sT[j]
			r=rT[j]
			ZZ=[g(k+1)-1+s for k in range(r)]
			Z.extend(ZZ)
		BL.append(Z)
	return BL
	
def SelfTransposableTP(M):	
	BL=[]
	r=len(M)
	ACh=AlgCharacterTable(M)
	CC=[sum([ACh[i][j]*(ACh[i][j].conjugate()) for i in range(r)]) for j in range(r)]
	dim=[ACh[i][0] for i in range(r)]
	CCC=[CC[0]/CC[i] for i in range(r)]
	dim2=[dim[i]**2 for i in range(r)]
	if not CCC==dim2:
			return False
	T=ListToType(CC)			
	NCh=[[dim[j]*ACh[i][j] for j in range(r)] for i in range(r)]
	l=len(T)
	rT=[t[1] for t in T]
	sT=[sum(rT[:i]) for i in range(l)]
	TG=[SymmetricGroup(i) for i in rT]
	LTG=[len(G) for G in TG]
	N=prod(LTG)
	for i in range(N):
		print(i,N)
		L=multibase(i,LTG)
		gL=[TG[j][L[j]] for j in range(l)]
		P=[]
		for j in range(l):
			g=gL[j]
			s=sT[j]
			rr=rT[j]
			ZZ=[g(k+1)-1+s for k in range(rr)]
			P.extend(ZZ)
		Ch=[[NCh[ii][P[j]] for j in range(r)] for ii in range(r)]
		MCh=matrix(Ch)
		if MCh==MCh.transpose():
			print(M); print(Ch)
			return True	
	return False								

def multibase(n, s):
	l=len(s)
	b=[]
	m=n
	for v in range(l):
		a=prod([s[i] for i in range(l-v-1)])
		c=m//a
		m=m-a*c
		b.append(c)
	b.reverse()
	return b

def IndexGiver(v):
	vv=list(str(v))
	s=''
	for ss in vv[1:]:
		s+=ss
	return int(s)

def IntDivCyclo(x):	#only for cyclo UCF
	n=CycloNorm(x)
	L=divisors(n)
	L.sort()
	r=len(L)
	for i in range(r):
		m=L[r-i-1]
		if '/' not in list(str(x/m)):
			return m
			
def AndersonMooreVafaMatrix(M):
	d=Duality(M)
	D=AlgDim(M)
	l=len(M)
	E0=[0 for ii in range(l)]
	EE=copy.deepcopy(E0)
	EE[0]=1	
	E=[EE]
	for i in range(l):
		if i<d[i]:
			EE=[0 for ii in range(l)]
			EE[i]=1
			EE[d[i]]=-1	
			E.append(EE)	#theta_i = theta_{i*}
	for i in range(l):
		for j in range(l):
			for m in range(l):
				for r in range(l):
					EE=copy.deepcopy(E0)
					Nijmr=sum([M[i][j][p]*M[p][m][r] for p in range(l)])
					EE[i]+=Nijmr; EE[j]+=Nijmr; EE[m]+=Nijmr; EE[r]+=Nijmr
					for p in range(l):
						EE[p]-=M[i][j][p]*M[p][m][r]+M[i][m][p]*M[j][p][r]+M[j][m][p]*M[i][p][r]
					if EE!=E0:
						if EE not in E:
							E.append(EE)
	return E
	
def custom_mod(a, b):
    positive_rep = a % b
    negative_rep = positive_rep - b
    return negative_rep if abs(negative_rep) < positive_rep else positive_rep
	
def rational_reduce_mod_1(c):
    if c in QQ:
        # Reduce the numerator modulo the denominator
        return custom_mod(c.numerator(), c.denominator()) / c.denominator()
    else:
        # If the coefficient is not a rational number, return it unchanged (or handle other cases)
        return c
        
def SmithReduction(FM):
	n=len(FM)
	EE=AndersonMooreVafaMatrix(FM)
	ME=matrix(ZZ,EE)
	A, U, V = ME.smith_form()
	m=A[n-1][n-1]
	if m==0:
		return 'not the expected form 1'# prove that it is not possible	
	Q=[A[i][i] for i in range(n)]
	v=[]
	M=matrix(QQ,[[custom_mod(V[i][j],Q[j])/Q[j] for j in range(n)] for i in range(n)])
	#d=[lcm([a[i].denominator() for i in range(n)]) for a in M]
	X=[]
	ii=0
	for i in range(n):
		if Q[i]==1:
			X.append(0)
		else:
			X.append(var('k{}'.format(ii)))
			ii+=1
	v=vector(X)
	w=M*v
	pq=[[w[i].numerator(),Integer(w[i].denominator())] for i in range(n)]
	T=[E(pq[i][1])**pq[i][0] for i in range(n)]		
	return [w,diagonal_matrix(T),X,Q]
  
'''  
        
from itertools import combinations

def SmithReductionPlus(FM):	# This code uses the Smith normal form plus an improvement to diagonalize V as much as possible "in some sense", 
	n=len(FM)		# to maximize the number of entries in T-matrix with a single parameter, and then reduces the number of cases and optimizing the application of nonzero trick
	EE=AndersonMooreVafaMatrix(FM)
	ME=matrix(ZZ,EE)
	A, U, V = ME.smith_form(); #print(list(U), 1, list(1/U))
	m=A[n-1][n-1]
	if m==0:
		return 'not the expected form 1'# prove that it is not possible	
	Q=[A[i][i] for i in range(n)]; print(Q)
	v=[]
	M=matrix(QQ,[[custom_mod(V[i][j],Q[j])/Q[j] for j in range(n)] for i in range(n)]); 
	d=[lcm([a[i].denominator() for i in range(n)]) for a in M]; print(M,d)
	# Compute the rank over Q.
	rank_r = M.rank()
	
	# Find a subset of rows that are independent with minimal product of d_i.
	# This will require iterating over combinations of rows and checking for independence.
	min_prod = +Infinity
	best_combination = None
	
	for row_indices in combinations(range(n), rank_r):	# future update: order by prod_di to avoid useless computation
		submatrix = M.matrix_from_rows(row_indices)
		if submatrix.rank() == rank_r:  # Check if rows are independent
			# Calculate the product of corresponding d_i values.
			prod_di = prod([d[i] for i in row_indices])
			if prod_di < min_prod:
				min_prod = prod_di
				best_combination = row_indices
	# Now best_combination contains the indices of the independent rows with minimal product of d_i.
	
	independent_rows = M.matrix_from_rows(best_combination)
	
	# the remaining variables.		
	X=[]
	ii=0
	for i in best_combination:
		if d[i]==1:
			X.append(0)
		else:
			X.append(var('k{}'.format(ii)))
			ii+=1
	d2=[d[i] for i in best_combination]
	#print(d,best_combination,d2)
	w=[]
	deno=[d2[j] for j in range(rank_r)]
	for i in range(n):
		# For each row not in the independent set, express it as a linear combination of the independent rows.
		if i not in best_combination:
			row_to_express = vector(QQ,M.row(i))
			# Solve the linear system to express the row in terms of the independent rows.
			coefficients = independent_rows.transpose().solve_right(row_to_express)
			deno = [lcm(deno[j],coefficients[j].denominator()) for j in range(rank_r)]; #print(d2,deno,coefficients) ############### it looks to strong
			w.append(sum([coefficients[j]*X[j]/d2[j] for j in range(rank_r)]))		# warning: if coeff has a denominator!=1 then d2 should be reevaluate (because new variability) 
		# if the row is in the independent set
		if i in best_combination:
			i2=best_combination.index(i)
			w.append(X[i2]/d2[i2])
	# make the T-matrix		
	pq=[[w[i].numerator(),Integer(w[i].denominator())] for i in range(n)]
	T=[E(pq[i][1])**pq[i][0] for i in range(n)]		
	return [w,diagonal_matrix(T),X,d2]   #,deno]
			     
        

# Apply the function to each coefficient of the expression
expr_rational_mod_1 = expr.apply_map(lambda x: rational_reduce_mod_1(x))

# Print the result
print(expr_rational_mod_1)
	
	
def SmithReductionPlus(M):	# This code uses the Smith normal form plus an improvement to "in some sense" diagonalize V as much as possible, 
	l=len(M)		# to maximize the number of entries in T-matrix with a single parameter, and then reduces the number of cases and optimizing the application of nonzero trick
	EE=AndersonMooreVafaMatrix(M)
	ME=matrix(ZZ,EE)
	A, U, V = ME.smith_form(); #print(A,V)
	m=A[l-1][l-1]
	if m==0:
		return 'not the expected form 1'# prove that it is not possible
	#R = IntegerModRing(m); print(m)
	#M_mod_m = Matrix(R, ME)
	#Dm, Um, Vm = M_mod_m.smith_form(); print(Dm, Vm)	
	Q=[A[i][i] for i in range(l)]
	v=[]
	VV=matrix(QQ,[[custom_mod(V[i][j],Q[j]) for j in range(l)] for i in range(l)]); #print(VV,Q)
	#AB, UB, VB = VV.smith_form(); print(AB,UB,VB)
	V3=matrix(QQ,[[custom_mod(V[i][j],Q[j])/Q[j] for j in range(l)] for i in range(l)]) #print(VV,V3)
	lc=[lcm([a[i].denominator() for i in range(l)]) for a in V3]
	return V3,lc
	#V4=matrix(ZZ,[list(lc[i]*V3[i]) for i in range(l)]); print(lc,V4, list(V4), rank(V4))
	L=[list(lc[i]*V3[i]) for i in range(l)]
	Q1=[]
	lc1=[]; #print(lc)
	for i in range(l):
		if Q[i]!=1:
			Q1.append(i)
		if lc[i]!=1:
			lc1.append(i)
	L1=[[L[i][j] for j in Q1] for i in lc1]; 
	ML1=matrix(ZZ,L1); r1=rank(ML1)
	ML2=ML1[:r1]	
	if ML2.determinant()!=0:# what if ML2 is not invertible? Find another one invertible
		print(1/ML2,ML1,ML1/ML2)		# extra restriction on the parameters: the application of the vector of parameter to ML1/ML2 should be integer vector
	X=[var('k{}'.format(i)) for i in range(l)]
	#R=PolynomialRing(QQ,l,"k")
	#R.inject_variables()
	#X=list(R.gens())
	for i in range(l):
		if Q[i]==1:
			v.append(0)
		else:
			v.append(X[i]/Q[i])			
	vv=vector(v)
	w=VV*vv
	#R=PolynomialRing(QQ,l,"k")
	#w=[SR(sum(rational_reduce_mod_1(c) * b for c, b in list(R(ww[i])))) for i in range(l)]
	pq=[[w[i].numerator(),Integer(w[i].denominator())] for i in range(l)]
	T=[E(pq[i][1])**pq[i][0] for i in range(l)]		
	return [list(w),diagonal_matrix(T),X,Q]	
	
#T.append(E(q)**p)
#p=s.numerator()
#q=Integer(s.denominator())


from itertools import combinations

# Assume M is your nxn matrix over Q and d is your vector of positive entries.
n = M.nrows()

# Convert the matrix to one over the rationals, if it's not already.
M_Q = Matrix(QQ, M)

# Compute the rank over Q.
rank_r = M_Q.rank()

# Find a subset of rows that are independent with minimal product of d_i.
# This will require iterating over combinations of rows and checking for independence.
min_prod = +Infinity
best_combination = None

for row_indices in combinations(range(n), rank_r):	#order by prod_di to avoid useless computation
    submatrix = M_Q.matrix_from_rows(row_indices)
    if submatrix.rank() == rank_r:  # Check if rows are independent
        # Calculate the product of corresponding d_i values.
        prod_di = prod([d[i] for i in row_indices])
        if prod_di < min_prod:
            min_prod = prod_di
            best_combination = row_indices

# Now best_combination contains the indices of the independent rows with minimal product of d_i.

# To express other rows in terms of the independent rows, you can create an augmented matrix
# with the independent rows and solve the linear system for each of the other rows.
independent_rows = M_Q.matrix_from_rows(best_combination)

# For each row not in the independent set, express it as a linear combination of the independent rows.
for i in range(n):
    if i not in best_combination:
        row_to_express = vector(QQ,M_Q.row(i))
        # Solve the linear system to express the row in terms of the independent rows.
        coefficients = independent_rows.transpose().solve_right(row_to_express)
        print(f"Row {i} can be expressed as {coefficients} in terms of rows {best_combination}")

'''		


'''
def TmatrixEquations(M,nn):	## nn is for the conductor, put -1 for no constraint
	d=Duality(M) 	#print(d)
	D=AlgDim(M)	#modified from int to cyclo int
	l=len(M)
	X=[var('x%d' % i) for i in range(l)]
	#N=[[[[sum([M[i][j][p]*M[p][m][r] for p in range(l)]) for r in range(l)] for m in range(l)] for j in range(l)] for i in range(l)]
	E=[X[0]]
	for i in range(l):
		if i!=d[i]:
			E.append(X[i]-X[d[i]])		#theta_i = theta_{i*}
	if nn==-1:	
		n=SqrtDInt(IntDivCyclo(D^5))
	else:
		n=nn
	print('conductor = ', n)
	ZN=Integers(n)	# Ring of integers modulo n
	R=PolynomialRing(ZN,l,"x")
	R.inject_variables()
	for i in range(l):
		for j in range(l):
			print([i,j])
			for m in range(l):
				for r in range(l):
					#print([i,j,m,r],len(E),E)
					MP=[M[i][j][p]*M[p][m][r]+M[i][m][p]*M[j][p][r]+M[j][m][p]*M[i][p][r] for p in range(l)]
					Nijmr=sum([M[i][j][p]*M[p][m][r] for p in range(l)])
					eq=(X[i]+X[j]+X[m]+X[r])*(Nijmr)-sum([X[p]*MP[p] for p in range(l)])
					#if not (eq in E):
					E.append(eq)
		E=list(set(E))
		Id=R.ideal(E)
		G=Id.groebner_basis()
		E=[g for g in G]	#print(len(E),E)
	#print(E)
	Id=R.ideal(E)
	G=Id.groebner_basis(); print(Id)
	GG=my_basis(ideal(G)); #print([g for g in GG])
	#Idim=Id.dimension()
	#print('dimension=', Idim)
	#if Idim==0:
	#print(Id.variety(ZN))	# the solution should then be divided by n
	return [n,GG,list(R.gens())]

# [x0, x1 + x2 + 3*x3, 2*x2, 2*x3, 4*x4 - 4*x5 - 4*x6, 8*x5, 8*x6, 32*x7 - 32*x8 + 32*x9, 64*x8, 64*x9]

def LinearEquationToList(g,V):
	#print(g,V)
	lg=list(g)
	return [[l[0],V.index(l[1])] for l in lg]
	
def preTmatrix(M,nn):	#this code is designed only for the shape of G above at rank <= 10 (integral case), i.e. linear w/o constant, Groebner basis	#improve this part
	l=len(M)	## nn is for the conductor, put -1 for no constraint
	if l==1:
		return [[0],diagonal_matrix([1]),[0],[1]]
	[n,G,V]=TmatrixEquations(M,nn)				# integral no more required
	return preTmatrixInter(n,G,V)

def preTmatrixInter(n,G,V):
	l=len(V)	# we want len(M) but always = len(V), right?
	lV=len(V)
	lG=len(G)
	VK=[var('k%d' % i) for i in range(lV)]
	if l==2:
		return [[0,VK[1]/4],diagonal_matrix([1,E(4)**VK[1]]),[0,VK[1]],[1,4]]
	if lV!=lG:						# add the cases [0], [1]
		return 'not the expected form 1'
	T=[]; arg=[]
	BL=[[] for i in range(lV)]
	K=[[] for i in range(lV)]
	for i in range(lG):
		ii=lG-i-1
		g=G[ii]
		Lg=LinearEquationToList(g,V)
		Lg00=Integer(Lg[0][0])
		if Lg00==1:
			VK[ii]=0
		s=VK[ii]/Lg00
		for ll in Lg[1:]:
			if BL[ll[1]]==[]:
				print(ii,BL)
				return 'not the expected form 2'
			s-=BL[ll[1]]*best(Integer(ll[0]),n)/Lg00
		BL[ii]=s
		K[ii]=Lg00
		p=s.numerator()
		q=Integer(s.denominator())
		T.append(E(q)**p)
		arg.append(s)
	T.reverse()
	arg.reverse()
	#print(T)
	return [arg,diagonal_matrix(T),VK,K]
'''

def best(m,n):
	a=m%n
	if a<=n/2:
		return a
	else:
		return -(-a%n)	

def BestQ(x):
	p=Integer(x.numerator())
	q=Integer(x.denominator())
	pp=Integer(best(p,q))
	return pp/q

def SumListStr(L):
	a=''
	for aa in L:
		a+=aa
	return a


#### Max code ####

import itertools
from sage.rings.finite_rings.integer_mod_ring import crt as mycrt

def myinterreduced_basis(J):
    B = J.basis
    R = J.basis[0].parent()
    while True:
        newB = []
        for b in B:
            r = R.ideal(list(set(B)-{b})).reduce(b)	# to reduce properly over the ring of interger modulo n, n should not be too big (210^4 ok, but 210^5 not, 2^32?), otherwise it returns that the ring should be a field... 	
            if r:
                newB.append(r)
        if newB == B:
            break
        B = newB
    return B


def myroots(p):
    R = p.base_ring()
    #if not isinstance(R,sage.rings.abc.IntegerModRing):
    #   yield from p.roots(multiplicities=False)
    #    return

    m = R.zero().modulus()
    pz = p.change_ring(ZZ)
    g = gcd(gcd(pz.coefficients()),m)
    mg = m//g

    roots = (pz/g).roots(ring=Integers(mg),multiplicities=False)  # roots modulo mg = m/g

    # embedding roots modulo mg to modulo m=mg*g
    for rr in itertools.product( *( [Mod(r*q^valuation(mg,q),q^k) for r in range(q^valuation(g,q))] for q,k in factor(m) ) ):
        r2 = mycrt(rr)
        yield from (r2 + ZZ(r) for r in roots)
        
def myvariety(sys,vars=None):
    J = ideal( sys )
    R = J.ring()

    if vars==None:
        vars = R.gens()
    if len(vars)==0:
        return [dict()]

    T = list()

    v = vars[0]
    nvars = vars[1:]

    B = J.elimination_ideal(nvars).basis

    assert len(B) == 1
    assert B[0] != 0

    for q in myroots(B[0].univariate_polynomial()):
        S = myvariety( [r.subs({v:q}) for r in myinterreduced_basis(J)], nvars )
        for s in S:
            s.update({v:q})
        T += S
    return T

#### end Max code ####


def SqrtDInt(D):
	L=list(factor(D))
	return prod([l[0]**(l[1]//2) for l in L])

def lcmNonzero(L):
	LL=[]
	for l in L:
		if l!=0:
			LL.append(l)
	return lcm(LL)

def ListToT(TT):
	return [E(t.denominator())**(t.numerator()) for t in TT]

def MtoDualityMat(M):
	r=len(M)
	return [[M[i][j][0] for i in range(r)] for j in range(r)]

def MatrixToList(M):
	r=len(M)
	return [[M[i][j] for j in range(r)] for i in range(r)]

def CycloNorm(D):				# too complicated, just pick the constant term
	f=UCF(D).minpoly()
	return f(0).abs()

def SqrtUCF(D):		# here the non-integral problem, sqrt(D) not always UCF
	f=UCF(D).minpoly()
	R.<t> = PolynomialRing(QQ)
	g=f(t^2)
	K.<a> = g.splitting_field(); print(K)
	if not K.is_abelian():
		return [False]		#no cyclo sqrt
	else:
		n=K.conductor()
		LL=g.roots(CyclotomicField(n))
		L=[UCF(x[0]) for x in LL]
		for x in L:
			if x^2==D and x>=0:
				return [True, x]
	return [False, 'MistakeSqrtUCF']

def StepsFinder(LLA):
	St=[0]
	for l in LLA:
		if len(l)==1:
			li=l[0]
			if LLA[li]!=[li]:
				return 'not the expected shape'	
			ww=0
			for j in range(li):
				if LLA[j]!=[] and max(LLA[j])>li:
					ww=1
					break
			if ww==0:
				St.append(li)
	return St

def Checked(S,T,M):	# (3.1.2) in Bakalov-Kirilov
	r=len(M)
	for i in range(r):
		for j in range(r):
			if T[i]*T[j]*S[i][j]!=sum([M[i][k][j]*T[k]*S[k][0] for k in range(r)]):
				print([i,j])
				print(T[i]*T[j]*S[i][j])
				print(sum([M[i][k][j]*T[k]*S[k][0] for k in range(r)]))
				return False
	return True

def FromTMtoS(T,M,dim):	# here T is just the diagonal
	r=len(M)
	return [[(sum([M[i][k][j]*T[k]*dim[k] for k in range(r)]))/(T[i]*T[j]) for j in range(r)] for i in range(r)]

def Verlinde(S):
	r=len(S)
	D=sum([S[i][0]**2 for i in range(r)])
	return [[[sum([S[l][i]*S[l][j]*(S[l][k].conjugate())/S[l][0] for l in range(r)])/D for k in range(r)] for j in range(r)] for i in range(r)]


# Warning STmatrix2 has no solution for [[[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], [[0, 1, 0, 0, 0], [0, 0, 1, 1, 0], [1, 0, 0, 0, 1], [0, 0, 1, 0, 1], [0, 1, 0, 1, 1]], [[0, 0, 1, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 1]], [[0, 0, 0, 1, 0], [0, 0, 1, 0, 1], [0, 1, 0, 0, 1], [1, 0, 0, 1, 1], [0, 1, 1, 1, 1]], [[0, 0, 0, 0, 1], [0, 1, 0, 1, 1], [0, 0, 1, 1, 1], [0, 1, 1, 1, 1], [1, 1, 1, 1, 2]]]
# whereas STmatrix has (STmatrix2 no more updated to non-integral case?)

def STmatrix2(MZ):							# much better than STmatrix?			## nn is for the conductor, put -1 for no constraint
	M=SortFusionData(MZ)						# if pk too big then try STmatrix first (it was useful in practice)
	BL=[]								# Warning: filter by ModularCriterion or SelfTransposable first
	MD=[]
	dim=[round(matrix(m).norm()) for m in M]		# warning: only for the integral case
	D=sum([a^2 for a in dim])
	[arg,MT,VK,KK]=SmithReduction(M)#preTmatrix(M,nn)
	RR=PolynomialRing(QQ,len(VK),"k")
	RR.inject_variables()
	LArg=[list(RR(ar)) for ar in arg]; print(arg,LArg,VK)
	LLB=[[[ll[0],VK.index(ll[1])] for ll in l] for l in LArg]
	#LLA=[[bb[1] for bb in b] for b in LLB]
	pK=prod(KK); print('pK = ', pK)
	LC=MtoDualityMat(M)
	C=matrix(LC)
	for i in range(pK):
		print('i=', i)
		LK=multibase(i,KK)
		TT=[BestQ(QQ(sum([bb[0]*LK[bb[1]] for bb in b]))) for b in LLB]
		T=ListToT(TT)
		S=FromTMtoS(T,M,dim)
		#print(S,T,M,dim,TT,D,C)
		SL=TestST(S,T,M,dim,TT,D,C) #; print(SL)
		if SL!=False:
			[orS,orT,c,nu2] = SL
			#print([S,TT,dim,orS,orT,c,nu2])
			NS,NT=NormalForm(S,TT)
			if not [NS,NT] in BL:	# if 1==1:						# replace by normal form??
				MM=Verlinde(S)		# Here keep S, do not put NS. We just moved from before TestST to here, relevant?
				if MM==M:		# always True?
					#print(M)
					MD.append([M,S,TT,dim,orS,orT,c,nu2]); print([M,S,TT,dim,orS,orT,c,nu2]) 
					BL.extend(IsoClassModularData(NS,NT))		# replace by normal form??
	print(len(MD))
	return MD

def ComponentOrdering(TT,dim):
	Ty=ListToType(dim)
	L=[0]
	i=0
	for l in Ty:
		i+=l[1]
		L.append(i)
	T=[]
	for i in range(len(L)-1):
		K=TT[L[i]:L[i+1]]
		K.sort()
		T.extend(K)
	return T

def STmatrixCO(M):	# for pointed only (much quicker)		# WARNING: double-check that ComponentOrdering is ok in the pointed case
	BL=[]			# we know that T-matrix is enough for the pointed case
	MD=[]
	dim=[round(matrix(m).norm()) for m in M]
	D=sum([a^2 for a in dim])
	[arg,MT,VK,KK]=SmithReduction(M)#preTmatrix(M,nn)
	RR=PolynomialRing(QQ,len(VK),"k")
	RR.inject_variables()
	LArg=[list(RR(ar)) for ar in arg]; print(arg,LArg,VK)
	LLB=[[[ll[0],VK.index(ll[1])] for ll in l] for l in LArg]
	#LLA=[[bb[1] for bb in b] for b in LLB]
	pK=prod(KK); print('pK = ', pK)
	LC=MtoDualityMat(M)
	C=matrix(LC)
	for i in range(pK):
		print('i=', i)
		LK=multibase(i,KK)
		TT=[BestQ(QQ(sum([bb[0]*LK[bb[1]] for bb in b]))) for b in LLB]
		T=ListToT(TT)
		S=FromTMtoS(T,M,dim)
		MM=Verlinde(S)
		if MM==M:		# always True?
			#print(S,T,M,dim,TT,D,C)
			SL=TestST(S,T,M,dim,TT,D,C)
			if SL!=False:
				CO=ComponentOrdering(TT,dim)				
				if not CO in BL:
					[orS,orT,c,nu2] = SL
					MD.append([M,S,TT,dim,orS,orT,c,nu2])
					BL.append(CO) 
	print(len(MD))
	return MD		

def TestST(S,T,M,dim,TT,D,C):		# in comment of this code 'excluded Theorem 2.1 (a.b)' means Theorem 2.1 (a) of ng-rowell-wang-wen paper, b-th relation (warning: b is not written in their paper)   
	r=len(T)
	orSL=[]
	SqD=SqrtUCF(D); #print('step 0')
	if not SqD[0]:
		print('sqrt(dim) not cyclo')
		return False
	SD=SqD[1]
	for i in range(r):
		for j in range(r):
			#print('step 1', UCF(S[i][j]),dim[j], UCF(S[i][j]/dim[j]))
			if not (UCF(S[i][j]/dim[j])).is_integral():
				print('excluded by Theorem 2.1 (4.1)')
				return False
			#K.<a> = NumberField((UCF(S[i][j])).minpoly())
			orSL.append((UCF(S[i][j])).conductor())	#orSL.append(K.conductor()) # why not just (UCF(S[i][j])).conductor() ????? It is much quicker!!
	orS=lcm(orSL)
	orT=lcm([t.denominator() for t in TT]); #print('step 2')
	if orT%orS!=0 or prime_factors(orT)!=prime_factors(CycloNorm(D)):
		print('excluded by Theorem 2.1 (4.2) or (6)')
		return False
	pplus=sum([(dim[i]**2)*T[i] for i in range(r)])
	pminus=sum([(dim[i]**2)/T[i] for i in range(r)]); #print('step 3')
	if pminus==0 or (pminus!=0 and (pplus/pminus).multiplicative_order()==+Infinity):
		print('excluded Theorem 2.1 (5.1)')
		return False
	ps=UCF(pplus/SD)
	mp=ps.multiplicative_order(); #print('step 4')
	if mp==+Infinity:
		print('excluded Theorem 2.1 (5.2)')
		return False
	for p in range(mp):
		if ps==E(mp)**p:
			c=Integer(best(8*p,8*mp))/Integer(mp)
			break
	MT=diagonal_matrix(T)	
	MS=matrix(S); #print('step 5')
	if MS**2 != D*C:
		print('excluded Theorem 2.1 (5.3)')
		return False
	AA=(MS*MT)**3; CC=pplus*D*C; #print('step 6')
	if AA != CC:
		print('excluded ProjRep')
		return False
	nu1=[sum([M[j][k][i]*(dim[j]*(T[j]**1))*((dim[k]*(T[k]**1)).conjugate()) for j in range(r) for k in range(r)])/D for i in range(r)]
	nu2=[sum([M[j][k][i]*(dim[j]*(T[j]**2))*((dim[k]*(T[k]**2)).conjugate()) for j in range(r) for k in range(r)])/D for i in range(r)]
	nnu1=[0 for i in range(r)]
	nnu1[0]=1; #print('step 7')
	if nu1!=nnu1:
		print('excluded Theorem 2.1 (8.1)')
		return False
	for i in range(r):
		#print('step 8')
		if C[i][i]!=1:
			if nu2[i]!=0:
				print('excluded Theorem 2.1 (8.2)')
				return False
		else:
			#print('step 9')
			if not 	nu2[i] in [-1,1]:
				print('excluded Theorem 2.1 (8.3)')
				return False	
	return [orS,orT,c,nu2]

def MagicCriterion(FD):
	M=SortFusionData(FD)
	r=len(M)
	V=preSmatrix(M)
	if V[0]:
		LC=MtoDualityMat(M)
		[arg,MT,VK,KK] = SmithReduction(M)
		NV=[]
		for SM in V[1]:
			sm=0
			for i in range(r):
				if ((matrix(SM)*MT)**3)[i][LC[i].index(1)] == 0: # looking for nonzero entry on (ST)^3 at the '1' entries of the duality matrix LC = (1/d)S^2
					sm=1
					break
			if sm==0:
				NV.append(SM)
		return len(NV)!=0		
	return False
			
			
def STmatrix(MZ,Cut,Part):					# Cut is the nb of part to divide pK, Part varies between 0 and Cut (the last is the rest)
	M=SortFusionData(MZ)
	if (1-prod([matrix(m).norm() for m in M])).abs()<0.0001:
		return 'pointed, use STmatrix2 or STmatrixCO'
	MD=[]
	BBL=[]
	r=len(M)
	V=preSmatrix(M)
	if V[0]:
		S=V[1][0]
		dim=S[0]
		for d in dim:
			if d!=d.conjugate():
				aaaaaa=0; print('excluded by Theorem 2.1 (3.1)')
				return []
		D=sum([d**2 for d in dim])	# WARNING: in ng-rowell-wang-wen paper, that is D^2
		SqD=SqrtUCF(D)
		if not SqD[0]:
			print('excluded by Theorem 2.1 (5)','sqrt(dim) not cyclo')
			return []
		SD=SqD[1]
		MS=matrix(S)
		#if M != Verlinde(S):
		if MS*(MS.conjugate_transpose()) != D*identity_matrix(r):
			aaaaaa=0; print('excluded by Theorem 2.1 (3.2)')
			return []
		orSL=[]
		for i in range(r):
			for j in range(r):
				if not (UCF(S[i][j]/dim[j])).is_integral():
					aaaaaa=0; print('excluded by Theorem 2.1 (4.1)')
					return []
				#K.<a> = NumberField((UCF(S[i][j])).minpoly())
				orSL.append((UCF(S[i][j])).conductor())	#orSL.append(K.conductor()) # why not just (UCF(S[i][j])).conductor() ????? It is much quicker!!
		orS=lcm(orSL)
		AAAAAA=SmithReduction(M)#preTmatrix(M,nn)#
		if AAAAAA=='not the expected form 1':
			print(AAAAAA)
			return []	#ok because the cyclo conductor is finite
		[arg,MT,VK,KK]=AAAAAA
		LC=MtoDualityMat(M)
		C=matrix(LC)
		pK=prod(KK); print('pK=',pK)
		lV1=len(V[1])
		NV=[]		# new set of S-matrix satisfying below nonzero entry criterion on (ST)^3 at the '1' entries of the duality matrix LC = (1/d)S^2
		for SM in V[1]:
			sm=0
			for i in range(r):
				if ((matrix(SM)*MT)**3)[i][LC[i].index(1)] == 0:
					sm=1
					break
			if sm==0:
				NV.append(SM)
		if len(NV)==0:	
			print('excluded by Magic Criterion')	# Magic criterion: all too big pK examples can be excluded here.  		
			return []
		RR=PolynomialRing(QQ,len(VK),"k")
		RR.inject_variables()
		#print(arg)
		LArg=[list(RR(ar)) for ar in arg]#; print(arg,LArg,VK)
		LLB=[[[ll[0],VK.index(ll[1])] for ll in l] for l in LArg]
		pKc=pK//Cut
		pKr=pK%Cut
		Beg=pKc*Part
		En=min(pKc*(Part+1),pK)
		for i in range(Beg,En):
			print([i,pK])
			LK=multibase(i,KK)
			TT=[BestQ(QQ(sum([bb[0]*LK[bb[1]] for bb in b]))) for b in LLB]
			#print('arg T', TT)
			orT=lcm([t.denominator() for t in TT])
			ND=CycloNorm(D)
			if orT%orS!=0 or prime_factors(orT)!=prime_factors(ND):
				aaaaaa=0 ; print('excluded by Theorem 2.1 (4.2) or (6)') #; print(D,CycloNorm(D),prime_factors(CycloNorm(D)))
			else:
				T=ListToT(TT)
				pplus=sum([(dim[i]**2)*T[i] for i in range(r)])
				pminus=sum([(dim[i]**2)/T[i] for i in range(r)])
				if pminus==0 or (pminus!=0 and (pplus/pminus).multiplicative_order()==+Infinity):
					aaaaaa=0; print('excluded Theorem 2.1 (5.1)')
				else:
					ps=UCF(pplus/SD)
					mp=ps.multiplicative_order()
					if mp==+Infinity:
						aaaaaa=0; print('excluded Theorem 2.1 (5.2)')
					else:
						for p in range(mp):
							if ps==E(mp)**p:
								c=Integer(best(8*p,8*mp))/Integer(mp)
								aaaaaa=0#print('central charge = ', c)
								break
						MT=diagonal_matrix(T)	
						if MS**2 != D*C:
							aaaaaa=0; print('excluded Theorem 2.1 (5.3)')
						else:
							for AS in NV:
								MS=matrix(AS); AA=(MS*MT)**3; CC=pplus*D*C
								if AA != CC:
									print('excluded ProjRep')
								else:	
									nu1=[sum([M[j][k][i]*(dim[j]*(T[j]**1))*((dim[k]*(T[k]**1)).conjugate()) for j in range(r) for k in range(r)])/D for i in range(r)]
									nu2=[sum([M[j][k][i]*(dim[j]*(T[j]**2))*((dim[k]*(T[k]**2)).conjugate()) for j in range(r) for k in range(r)])/D for i in range(r)]
									nnu1=[0 for i in range(r)]
									nnu1[0]=1; #aaaaaa=0#print(nu1,nnu1,nu2)
									if nu1!=nnu1:
										aaaaaa=0; print('excluded Theorem 2.1 (8.1)')
									else:
										x=0
										for i in range(r):
											if C[i][i]!=1:
												if nu2[i]!=0:
													x=1
													aaaaaa=0; print('excluded Theorem 2.1 (8.2)')
													break
											else:
												if not 	nu2[i] in [-1,1]:
													x=1	
													aaaaaa=0; print('excluded Theorem 2.1 (8.3)')
													break
										if x==0:
											NS,NT = NormalForm(AS,TT)
											if not [NS,NT] in BBL:
												MD.append([M,S,TT,dim,orS,orT,c,nu2]); print([M,S,TT,dim,orS,orT,c,nu2]) 								
												BBL.extend(IsoClassModularData(NS,NT))
	print(len(MD))
	return MD	
	
'''
		LLA=[[bb[1] for bb in b] for b in LLB]; print(LLA)
		St=StepsFinder(LLA); print(St)
		#return [LArg,LLB,LLA,St]
		if type(St)==str:
			return St
		if pK>Bound:				# this bound should be increased (or decreased) according to relevance.
			#FakeMT=diagonal_matrix([var('x{}'.format(i)) for i in range(r)])
			#AA=(matrix(V[1][0])*MT)**3
			return [prod([((matrix(V[1][j])*MT)**3)[i][LC[i].index(1)] for i in range(r)]) for j in range(lV1)]
			for st in St[:-1]:		# here we just test whether (ST)^3 has no zero entry where S^2 is nonzero: very efficient!!! Maybe a criterion visible at the fusion ring level.
				sst=st+1		# recall that S^2 is just the duality matric LC
				pr=prod(KK[:sst])#; print('pretest', 'st =', st, 'pr =',pr, [lV1,r])
				kkk=0
				for iii in range(pr):
					#print([iii,pr])
					LK=multibase(iii,KK[:sst])
					TT=[BestQ(QQ(sum([bb[0]*LK[bb[1]] for bb in b]))) for b in LLB[:sst]]
					T=ListToT(TT)
					T.extend([MT[j][j] for j in range(sst,r)])
					MMT=diagonal_matrix(T)					# modify here: avoid the same MT name (even if no problem in this part)
					cccc=0
					for ii in range(lV1):
						AS=V[1][ii]
						MMS=matrix(AS); AA=(MMS*MMT)**3
						ccc=0
						for i in range(r):
							#print([iii,ii,i])
							if AA[i][LC[i].index(1)]==0:	# shortcut to rule out L[19] and others...
								ccc=1
								break
						if ccc==0:
							cccc=1		
					if cccc==1:
						kkk=1		
				if kkk==0:
					print('excluded by Theorem 2.1 (5.0)', 'st =',st)
					return []
			else:
				return 'consider more equations if pK is too big', 'pK =', pK
'''			

def MatrixToList(M):
	return [list(m) for m in M]	

def IsoClassModularData(S,T):	### Ideally, we should use a faithful normal form. But for now let us just use the entries of T: we can assume then to be ordered locally (i.e. for each d_i) and consider its symmetry group
	BL=[]
	L=S[0]
	NT,p=NormalType(L,T)
	SS,TT = PermST(S,T,p)
	P=TypePerms(NT)
	for i in range(len(P)):
		#print([i])
		p=P[i]
		Sp,Tp = PermST(SS,TT,p)
		if not [Sp,Tp] in BL:
			BL.append([Sp,Tp])
	return BL

def PermST(S,T,p):
	r=len(S)
	return [[S[p[i]][p[j]] for j in range(r)] for i in range(r)], [T[p[i]] for i in range(r)]

# When considering isomorphism classes, it is appropriate to adopt a \emph{normal form} by sorting the basic elements 
# according to their $\FPdim$ \emph{and} spin, and limit basis permutations to those preserving both.
	
def NormalForm(S,T):
	L=S[0]
	NT,p=NormalType(L,T)	
	return PermST(S,T,p)
	
def NormalType(L,T):
	LL=ListToType(L)
	NT=[]
	PT=[]
	c=0
	for l in LL:
		t=T[c:l[1]+c]
		st=sorted(t)
		p=find_permutation(t, st)
		PT.extend([i+c for i in p])
		dt=DirectListToType(st)
		for ll in dt:	
			NT.append([l[0],ll[1]])
		c+=l[1]
	return NT,PT
	

def find_permutation(list1, list2):
    if sorted(list1) != sorted(list2):
        raise ValueError("Lists are not permutations of one another.")

    # Make a copy of list1 to keep track of matched elements
    temp_list1 = list(list1)
    
    # Initialize an array to store permutation indices
    permutation_indices = []
    
    # For each element in list2, find its index in the temp_list1 and add to permutation_indices
    for item in list2:
        index = temp_list1.index(item)
        permutation_indices.append(index)
        
        # Now that this element has been matched, set it to None to avoid matching it again
        temp_list1[index] = None

    return permutation_indices

'''
# Example usage:
list1 = [1, 2, 2, 3]
list2 = [2, 3, 1, 2]

    
'''
	
			

'''
Now in the modular case (d_i^2) = (c_1/c_j) up to a permutation on j, and more strongly, 
there must be such a permutation making the matrix (S_{i,j}) = (λ_{i,j}*sqrt(c_1/c_j)) symmetric (i.e. self-transpose)
'''

#UCF=UniversalCyclotomicField()


'''

def TmatrixEquationsProd(M):
	D=AlgDim(M)	#modified from int to cyclo int
	l=len(M)
	T=[var('T%d' % i) for i in range(l)]
	N=[[[[sum([M[i][j][p]*M[p][m][r] for p in range(l)]) for r in range(l)] for m in range(l)] for j in range(l)] for i in range(l)]
	E=[T[0]-1]
	n=SqrtDInt(IntDivCyclo(D^5)) 
	print('conductor = ', n)
	for i in range(l):
		for j in range(l):
			for m in range(l):
				for r in range(l):
					MP=[M[i][j][p]*M[p][m][r]+M[i][m][p]*M[j][p][r]+M[j][m][p]*M[i][p][r] for p in range(l)]
					eq=(T[i]*T[j]*T[m]*T[r])**(N[i][j][m][r])-prod([T[p]**(MP[p]) for p in range(l)])
					E.append(eq)
	R=PolynomialRing(QQ,l,"T")
	R.inject_variables()
	Id=R.ideal(E)
	G=Id.groebner_basis()
	#EG=[g for g in G]
	#EG.extend([(T[i]**n)-1 for i in range(1,l)])
	#Id=R.ideal(EG)
	#G=Id.groebner_basis()
	Idim=Id.dimension()
	print('dimension=', Idim)
	if Idim==0:
		print(Id.variety(CyclotomicField(n)))
	return [g for g in G]


def TmatrixEquationsGert(M):
	d=Duality(M)
	r=len(M)
	T=[var('t%d' % i) for i in range(r)]
	#N=[[[[sum([M[i][j][d[n]]*M[k][l][n] for n in range(r)]) for l in range(r)] for k in range(r)] for j in range(r)] for i in range(r)]
	E=[]
	for i in range(r):
		for j in range(r):
			for k in range(r):
				for l in range(r):
					E.append(sum([M[i][j][d[n]]*M[k][l][n]*(T[i]+T[j]+T[k]+T[l])-(M[i][j][n]*M[l][n][d[k]]+M[j][k][n]*M[l][n][d[i]]+M[i][k][n]*M[l][n][d[j]])*T[n] for n in range(r)]))
	R=PolynomialRing(QQ,r,"t")
	R.inject_variables()
	Id=R.ideal(E)
	G=Id.groebner_basis()
	return G
'''	

'''
#Max code for symmetrizable matrix

# matrix size
n = 10

# generate a random symmetric n X n 01-matrix
M = Matrix(ZZ,n,n)
for i in range(n):
    for j in range(i+1):
        M[i,j] = M[j,i] = randint(0,1)

# randomly permute columns of M
p = SymmetricGroup(n).random_element()
M = M[:,list(p(i)-1 for i in (1..n))]

# problem instance is created, let's now try to solve it

# define an ILP problem
milp = MixedIntegerLinearProgram()
milp.set_objective( None )

# permutation matrix to be found
Q = milp.new_variable(binary=True)
for i in range(n):
    milp.add_constraint( sum( Q[(i,j)] for j in range(n) ) == 1 )
    milp.add_constraint( sum( Q[(j,i)] for j in range(n) ) == 1 )

# constraints imposing that M*Q is symmetric
for i in range(n):
    for j in range(i):
        milp.add_constraint( sum( M[i,k] * Q[(k,j)] for k in range(n) ) == sum( M[j,k] * Q[(k,i)] for k in range(n) ) )

milp.solve()
R = Matrix( milp.get_values(Q) )

# print the permuted matrix, which should be symmetric
print(M*R)

'''



'''
###### old code #####

def preTmatrix(M):	#this code is designed only for the shape of G above at rank <= 10 (integral case), i.e. linear w/o constant, starting possibly by some xy=0 
	global BL
	l=len(M)
	if l==1:
		return [[0]]
	[n,G]=TmatrixEquations(M,-1)
	BL=[]
	G1=[]; G2=[]
	for g in G:
		d=g.degree()
		if d==2:
			G2.append(g)
		if d==1:
			G1.append(g)
	g=G1[-1]
	lg=list(g)
	if len(lg)!=1:
		return 'not the expected form 1'	# see:https://ask.sagemath.org/question/62787/all-the-solutions-of-a-polynomial-system-over-a-finite-ring/
	else:
		s=IndexGiver(lg[0][1])
		m=int(lg[0][0])
		p=n/gcd(m,n)
		for i in range(gcd(m,n)):
			F=[[] for i in range(l)]
			F[s]=p*i
			preTmatrixInter(G1[:-1],F,n)
	Lab=[]
	for g in G2:
		lg=list(str(g))
		if not '*' in lg:
			a=int(SumListStr(lg[1:-2]))
			b=a
			if len(lg)!=3+len(str(a)):
				print('not the expected form 2.1')
				return
		if '*' in lg:
			j=lg.index('*')
			a=int(SumListStr(lg[1:j]))
			b=int(SumListStr(lg[j+2:]))
			if len(lg)!=3+len(str(a))+len(str(b)):
				print('not the expected form 2.2')
				return
		Lab.append([a,b])
	NL=[]
	BLn=[]
	for l in BL:
		ln=[ll%n for ll in l]
		if not ln in BLn:
			BLn.append(ln)
	for l in BLn:
		for v in Lab:
			[a,b]=v
			if (l[a]*l[b])%n!=0:
				if not l in NL:
					NL.append(l)
				break
	S=[]
	for l in BLn:
		if not l in NL:
			S.append([i/n for i in l])
	return S

def preTmatrixInter(G,F,n):
	global BL
	#print(G,F,n)
	if G==[] and not [] in F:
		BL.append(F)
		return
	if G==[] and [] in F:
		ii=F.index([])
		for i in range(n):
			FF=copy.deepcopy(F)
			FF[ii]=i
			if [] in FF:
				print('not the expected form 3')
				return
			else:
				BL.append(FF)
		return
	g=G[-1]
	lg=list(g)
	ll=lg[0]
	c=0
	for l in lg[1:]:
		s=IndexGiver(l[1])
		m=int(l[0])
		p=n/gcd(m,n)
		if F[s]==[]:
			print('not the expected form 4')
			return
		else:
			c+=m*F[s]
	c=c%n
	ss=IndexGiver(ll[1])
	mm=int(ll[0])
	q=gcd(mm,n)
	pp=mm/q
	qq=n/q
	cc=(-c/pp)%n
	if cc%q==0:
		ccc=cc/q
		for i in range(q):
			FF=copy.deepcopy(F)	
			FF[ss]=(qq*i+ccc)%n
			preTmatrixInter(G[:-1],FF,n)


# some old parts #

			cccc=0
			lV1=len(V[1]); print('pretest', lV1, r)
			for ii in range(lV1):
				AS=V[1][ii]
				MMS=matrix(AS); AA=(MMS*MT)**3
				ccc=0
				for i in range(r):
					print([ii,i])
					if AA[i][LC[i].index(1)]==0:	# shortcut to rule out L[19]
						ccc=1
						break
				if ccc==0:
					cccc=1
			if cccc==0:
				print('excluded by Theorem 5.0')
				return []
			pr=1; ni=0
			while pr<100:				# maybe less still ok?
				pr*=KK[ni]
				ni+=1				# WARNING HERE: T[i] may require some k_j j>i, need to improve
			RR=PolynomialRing(QQ,ni+1,"k")		# if T[j] is single, it should be added. Should go up to a single
			RR.inject_variables()
			print(ni,pr)
			print(arg[:ni+1])
			print(KK[:ni+1])			# WARNING ni+1 here is just for [22], need to improve in general
			LArg=[list(RR(ar)) for ar in arg[:ni+1]]
			kkk=0
			pr*=KK[ni]

###

					ccc=0
					Eq=[]
					for i in range(r):
						print([ii,i])
						if AA[i][LC[i].index(1)]==0:	# shortcut to rule out L[19]
							ccc=1
							break
						for j in range(r):
							if LC[i][j]==0 and AA[i][j]!=0:
								Eq.append(AA[i][j])
					if ccc==0:
						AdEq.append([AS,Eq])
						cccc=1
				if cccc==1:
					kkk=1
					print('consider these equations')
					print(AdEq)
			if kkk==0:
				print('excluded by Theorem 5.0bis')
				return []
			else:
				return ('consider the equations')	
###

							kk=0
							for AS in V[1]:
								MS=matrix(AS); AA=(MS*MT)**3; CC=pplus*D*C
								if AA == CC:
									kk=1
									break
							if kk==0:
								aaaaaa=0; print('excluded Theorem 2.1 (5.4)')
							else:

'''
