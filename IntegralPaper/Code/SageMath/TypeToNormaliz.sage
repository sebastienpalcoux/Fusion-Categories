# %attach Nutstore/1/SAGE/TypeToNormaliz.sage
# %attach Nutstore Files/SAGE/TypeToNormaliz.sage

def TypeToNormaliz(l):
	T=ListToType(l)
	Du=duality(T)
	for d in Du:
		normaliz(l,d)

def TypeToNormalizSingle(l):
	T=ListToType(l)
	Du=duality(T)
	for d in Du:
		NormalizSingle(l,d)
		
def TypeToNormalizAlone(l):
	T=ListToType(l)
	Du=duality(T)
	for d in Du:
		NormalizAlone(l,d)		# dimension and associativity equations made by Normaliz
		
def TypeToNormalizAloneNC(l):
	T=ListToType(l); #print(l)
	l1=l[1:]
	if len(l1) != len(set(l1)):		# we can exclude the unit (since always selfdual)
		Du=duality(T)
		for d in Du:
			if d!=sorted(d):
				NormalizAlone(l,d)		# dimension and associativity equations made by Normaliz		

def TypeToNormalizC2Co(l):
	T=ListToType(l)
	Du=duality(T)
	for d in Du:
		d[0]=-3
		NormalizAlone(l,d)
		
def TypeToNormalizC2CoSingle(l):
	T=ListToType(l)
	Du=duality(T)
	for d in Du:
		d[0]=-3
		NormalizSingle(l,d)

def TypesToNormalizC2CoSingle(LL):
	for l in LL:
		print(l)
		TypeToNormalizC2CoSingle(l)		
		
def TypesToNormalizC2Co(LL):
	for l in LL:
		print(l)
		TypeToNormalizC2Co(l)	
		
def TypeToNormalizCo(l):
	T=ListToType(l)
	Du=duality(T)
	for d in Du:
		d[0]=-1
		NormalizAlone(l,d)

def TypeToNormalizSingleCo(l):
	T=ListToType(l)
	Du=duality(T)
	for d in Du:
		d[0]=-1
		NormalizSingle(l,d)

def TypeToNormalizAloneCo(l):
	T=ListToType(l)
	Du=duality(T)
	for d in Du:
		d[0]=-1
		NormalizAlone(l,d)
		
def TypeToNormalizSingleCoTrivial(l):
	T=ListToType(l)
	Du=duality(T)
	d=list(range(len(l)))
	d[0]=-1
	NormalizSingle(l,d)	

def TypeToNormalizModularOneGrad(l):
	T=ListToType(l)
	Du=duality(T)
	for d in Du:
		d[0]=-1
		NormalizModularOneGrad(l,d)		
		
def TypesToNormalizCo(LL):
	for l in LL:
		print(l)
		TypeToNormalizCo(l)	
		
def TypesToNormalizSingleCo(LL):
	for l in LL:
		print(l)
		TypeToNormalizSingleCo(l)						

def TypesToNormaliz(LL):
	for l in LL:
		print(l)
		TypeToNormaliz(l)

def TypesToNormalizSingle(LL):
	for l in LL:
		print(l)
		TypeToNormalizSingle(l)

def TypesToNormalizAlone(LL):
	for l in LL:
		print(l)
		TypeToNormalizAlone(l)
		
def TypesToNormalizAloneNC(LL):
	for l in LL:
		print(l)
		TypeToNormalizAloneNC(l)		
		
def TypesToNormalizSelfCo(LL):
	for l in LL:
		print(l)
		NormalizSelfCo(l)

		
def TypesToNormalizSelfSingle(LL):
	for l in LL:
		print(l)
		NormalizSelfSingle(l)

def TypesToNormalizStrong(LL):
	for l in LL:
		print(l)
		NormalizStrong(l)

def TypesToNormalizStrongFull(LL):
	for l in LL:
		print(l)
		NormalizStrongFull(l)
		
''' # for modular C2-grading, we can do as follows:
sage: LL=[]
....: for l in L:
....:     s=squareequipartitiontype(l)
....:     for ll in s:
....:         lll=[]
....:         for ss in ll:
....:             lll.extend(ss)
....:         LL.append(lll)

'''				

def TypesToPreNormaliz(LL):
	for l in LL:
		print(l)
		T=ListToType(l)
		prenormaliz(T)

def TypesToPreNormalizAlone(LL):
	for l in LL:
		print(l)
		PreNormalizAlone(l)		

def TypeToNormalizMNSD(l):	# it make sense to consider only the 12-term FrobRec (i.e. DoubleFrobRec), that is why Doublenormaliz
	T=ListToType(l)		
	d=dualityMNSD(T)
	Doublenormaliz(l,d)

def TypesToNormalizMNSD(LL):
	for l in LL:
		print(l)
		TypeToNormalizMNSD(l)
		
def TypeToNormalizAloneMNSD(l):		# without double, so maybe NC and Alone
	T=ListToType(l)		
	d=dualityMNSD(T)
	NormalizAlone(l,d)

def TypesToNormalizAloneMNSD(LL):
	for l in LL:
		print(l)
		TypeToNormalizAloneMNSD(l)		

def TypeToList(T):
	L=[]
	for t in T:
		L.extend([t[0] for i in range(t[1])])
	return L

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

def duality(T):
	t=len(T)
	F=[dualstructure(T[i][1],sum([T[j][1] for j in range(i)])) for i in range(t)]
	s=[len(F[i]) for i in range(t)]
	p=prod(s)
	l=[1]
	Du=[]
	for k in range(p):
		for v in range(1,t):
			l.extend(F[v][multibase(k,s)[v]])
		le=len(l)		
		ll=[l[f]-1 for f in range(le)]
		Du.extend([ll])
		l=[1]
	return Du

def dualityMNSD(T):
	t=len(T)
	F=[dualstructure(T[i][1],sum([T[j][1] for j in range(i)])) for i in range(t)]
	s=[len(F[i]) for i in range(t)]
	p=prod(s)
	l=[1]
	k=p-1
	for v in range(1,t):
		l.extend(F[v][multibase(k,s)[v]])
	le=len(l)		
	ll=[l[f]-1 for f in range(le)]
	return ll

def dualstructure(n,m):
	A=[]
	for i in range(1,n+2,2):
		l=[m+j for j in range(1,n-i+2)]
		l.extend([m+n-k+1 for k in range(1,i)])
		A.extend([l])
	return A

def multibase(n,s):
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

def normaliz(L,d):
	[A,V,M,Assoc]=System(L,d,0)
	s='['
	for i in L[:-1]:
		s+=str(i)+','
	s+=str(L[-1])+']['
	for i in d[:-1]:
		s+=str(i)+','
	s+=str(d[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space '+str(len(A[0]))+'\n')
	f.write('inhom_equations '+str(len(A))+'\n')
	for i in range(len(A)):
		A[i].append(-V[i])
	s=''
	for l in A:
		for ll in l:
			s+=str(ll)+' '
		s+='\n'
	f.write(s)
	f.write('LatticePoints'+'\n')
	f.write('convert_equations'+'\n')
	f.write('nonnegative'+'\n')
	f.write('polynomial_equations '+str(len(Assoc))+'\n')
	s=''
	for As in Assoc:
		li=list(str(As))
		j=0
		for i in li:
			if i==str(x):
				s+='x['
				j=1
			elif j==1 and i in {' ','*','^'}:
				s+=']'+i
				j=0
			else:
				s+=i
		if j==1:
			s+='];\n'
		else:
			s+=';\n'
	f.write(s)
	f.close()

def NormalizAlone(L,d):
	s='['
	for i in L[:-1]:
		s+=str(i)+','
	s+=str(L[-1])+']['
	for i in d[:-1]:
		s+=str(i)+','
	s+=str(d[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space auto'+'\n'+'fusion_type'+'\n'+str(L)+'\n'+'fusion_duality'+'\n'+str(d)+'\n'+'FusionData')
	f.close()
	
	
def NormalizModularOneGrad(L,d):
	s='['
	for i in L[:-1]:
		s+=str(i)+','
	s+=str(L[-1])+']['
	for i in d[:-1]:
		s+=str(i)+','
	s+=str(d[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space auto'+'\n'+'fusion_type'+'\n'+str(L)+'\n'+'fusion_duality'+'\n'+str(d)+'\n'+'FusionData'+'\n'+'UseModularGrading')
	f.close()	
	
def NormalizSingle(L,d):
	s='['
	for i in L[:-1]:
		s+=str(i)+','
	s+=str(L[-1])+']['
	for i in d[:-1]:
		s+=str(i)+','
	s+=str(d[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space auto'+'\n'+'fusion_type'+'\n'+str(L)+'\n'+'fusion_duality'+'\n'+str(d)+'\n'+'SingleLatticePoint')
	f.close()		

def NormalizSelfSingle(L):
	s='['
	for i in L[:-1]:
		s+=str(i)+','
	s+=str(L[-1])+']['
	d=list(range(len(L)))
	for i in d[:-1]:
		s+=str(i)+','
	s+=str(d[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space auto'+'\n'+'fusion_type'+'\n'+str(L)+'\n'+'fusion_duality'+'\n'+str(d)+'\n'+'SingleLatticePoint')
	f.close()
	
def NormalizSelfCo(L):
	s='['
	for i in L[:-1]:
		s+=str(i)+','
	s+=str(L[-1])+']['
	d=list(range(len(L)))
	d[0]=-1
	for i in d[:-1]:
		s+=str(i)+','
	s+=str(d[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space auto'+'\n'+'fusion_type'+'\n'+str(L)+'\n'+'fusion_duality'+'\n'+str(d)+'\n'+'FusionData')
	f.close()

def NormalizSelfCo(L):
	s='['
	for i in L[:-1]:
		s+=str(i)+','
	s+=str(L[-1])+']['
	d=list(range(len(L)))
	d[0]=-3
	for i in d[:-1]:
		s+=str(i)+','
	s+=str(d[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space auto'+'\n'+'fusion_type'+'\n'+str(L)+'\n'+'fusion_duality'+'\n'+str(d)+'\n'+'FusionData')
	f.close()	

def NormalizStrong(L):
	s='['
	for i in L[:-1]:
		s+=str(i)+','
	s+=str(L[-1])+']['
	d=list(range(len(L)))
	d[0]=-3
	for i in d[:-1]:
		s+=str(i)+','
	s+=str(d[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space auto'+'\n'+'fusion_type'+'\n'+str(L)+'\n'+'fusion_duality'+'\n'+str(d)+'\n'+'SingleLatticePoint')
	f.close()

def NormalizStrongFull(L):
	s='['
	for i in L[:-1]:
		s+=str(i)+','
	s+=str(L[-1])+']['
	d=list(range(len(L)))
	d[0]=-3
	for i in d[:-1]:
		s+=str(i)+','
	s+=str(d[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space auto'+'\n'+'fusion_type'+'\n'+str(L)+'\n'+'fusion_duality'+'\n'+str(d)+'\n'+'FusionData')
	f.close()
	
def PreNormalizAlone(L):
	s='['
	for i in L[:-1]:
		s+=str(i)+','
	s+=str(L[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space auto'+'\n'+'fusion_type_for_partition'+'\n'+str(L)) #+'\n'+'FusionRings' #now useless, check
	f.close()	

def PreNormalizAloneNW(L):
	s='['
	for i in L[:-1]:
		s+=str(i)+','
	s+=str(L[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space auto'+'\n'+'fusion_type_for_partition'+'\n'+str(L)+'\n'+'NoWeights') #+'\n'+'FusionRings' #now useless, check
	f.close()

def System(L,d,out):
	r=len(L)
	n=1		# Warning: need to put n=1 for the variables CoCoaLib version x[1], x[2], ..., but need n=0 for AA
	BL=[]
	V=[[[[] for k in range(r)] for j in range(r)] for i in range(r)]
	Vn=[[[[] for k in range(r)] for j in range(r)] for i in range(r)]
	vvar=[]
	for i in range(r):
		for j in range(r):
			l=[0,i,j]
			if not l in BL:
				FR=FrobRecList(d,l)
				BL.extend(FR)
				for ll in FR:
					[ii,jj,kk]=ll
					V[ii][jj][kk]=kronecker_delta(i,j)
					Vn[ii][jj][kk]=kronecker_delta(i,j)-2
	for i in range(r):
		for j in range(r):
			LVn=[]
			for k in range(r):
				l=[i,j,k]
				if l in BL:
					LVn.append(Vn[i][j][k])
				else:
					FR=FrobRecList(d,l)
					BL.extend(FR)
					v=var('x%d' % n)
					vvar.append(v)
					LVn.append(n)
					for ll in FR:
						[ii,jj,kk]=ll
						V[ii][jj][kk]=v
						Vn[ii][jj][kk]=n
					n+=1
	if out==0:				
		A=[[0 for j in range(n)] for i in range(r*r)]
		Ve=[]
		for i in range(r):
			for j in range(r):
				Ve.append(L[i]*L[j])
				for k in range(r):
					nn=Vn[i][j][k]
					if nn<0:
						nn+=2
						Ve[-1]-=L[k]*nn
					else:
						A[r*i+j][nn]+=L[k]
		AA=[]
		VVe=[]
		for i in range(r*r):
			if A[i]!=[0 for j in range(n)]:
				VVe.append(Ve[i])
				AA.append(A[i][1:])		# [1:] is just to fix n=1
			elif Ve[i]!=0:	
				return [[],[],[],[]]
		Assoc=[]
		for i in range(r):
			for j in range(r):
				for k in range(r):
					for t in range(r):
						eq=sum([V[i][j][s] * V[s][k][t] for s in range(r)]) - sum([V[j][k][s] * V[i][s][t] for s in range(r)])
						if eq!=0:
							Assoc.append(eq)
	if out==0:
		return [AA,VVe,V,set(Assoc)]
	if out==1:
		return [vvar,V]

def FrobRecList(d,l):
	[i,j,k]=l
	FR=[]
	T=[[i,j,k],[d[i],k,j],[j,d[k],d[i]],[d[j],d[i],d[k]],[d[k],i,d[j]],[k,d[j],i]]
	for t in T:
		if not t in FR:
			FR.append(t)
	FR.sort()
	return FR

def Var(L,d):
	V=[]
	BL=[]
	r=len(L)
	for i in range(r):
		for j in range(r):
			for k in range(r):
				l=[i,j,k]
				if (not 0 in l) and (not l in BL):
					FR=[[i,j,k],[d[i],k,j],[j,d[k],d[i]],[d[j],d[i],d[k]],[d[k],i,d[j]],[k,d[j],i]]
					BL.extend(FR)
					V.append(l)
	return V

def isomorphicclass(M,T,d):	### replace this code everywhere by a code computing a normal form (lex smallest vector formed by the N_ij^k where the the set of arguments i,j,k is itself ordered lex)
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
					MMM=[[[MM[g(k-c+1)-1+c][g(j-c+1)-1+c][g(i-c+1)-1+c] for i in range(ra)] for j in range(ra)] for k in range(ra)]
					if MMM not in LLM:
						LLM.append(MMM)
		LM=LLM
		c+=r
	return LM

def LListToFusion(LLL,LLd):
	r=len(LLL)
	for i in range(r):
		LL=LLL[i]
		[L,d]=LLd[i]
		print([L,d])
		ListToFusion(LL,L,d)

def ListToFusion(LL,L,d):
	mat=Makemat(L,d)
	BL=[]; ISOM=[]
	T=ListToType(L)
	for l in LL:
		M=mat(l)
		if not M in ISOM:
			print(M)
			BL.append(M)
			ISOM.extend(isomorphicclass(M,T,d))
	return BL

def ListToFusionBis(LL,L,d):
	mat=Makemat(L,d)
	BL=[]; ISOM=[]
	T=ListToType(L)
	for i in range(len(LL)):
		print(i)
		M=mat(LL[i])
		if not M in ISOM:
			#print(M)
			BL.append(M)
			ISOM.extend(isomorphicclass(M,T,d))
	return BL

def ListToFusionNonIso(LL,L,d):
	mat=Makemat(L,d)
	BL=[]
	T=ListToType(L)
	for l in LL:
		M=mat(l)
		print(M)
		BL.append(M)
	return BL

def ListToFusion2(LF,L,d):
	BL=[]; ISOM=[]
	T=ListToType(L)
	for M in LF:
		if not M in ISOM:
			print(M)
			BL.append(M)
			ISOM.extend(isomorphicclass(M,T,d))
	return BL

def VarToIndex(x):
	s=list(str(x))
	n=''
	for i in s[1:]:
		n+=i
	return eval(n)

def Makemat(L,d):
	[var,M]=System(L,d,1) #print(var)
	r=len(M)
	def mat(l):
		N=[]
		for i in range(r):
			NN=[]
			for j in range(r):
				NNN=[]
				for k in range(r):
					x=M[i][j][k]
					if x in [0,1]:
						NNN.append(x)
					else:
						n=VarToIndex(x)
						NNN.append(l[n-1])
				NN.append(NNN)
			N.append(NN)
		return N
	return mat

def PreSystem(T):	# dimension partition		# Warning: for the non-perfect the type should be written as [[1,1],[1,n],...]
	r=len(T)
	n=1		# Warning: need to put n=1 for the variables CoCoaLib version x[1], x[2], ..., but need n=0 for AA
	BL=[]
	Vn=[[[[] for k in range(r)] for j in range(r)] for i in range(r)]
	d=list(range(r))
	for i in range(r):
		for j in range(r):
			l=[0,i,j]
			if not l in BL:
				FR=FrobRecList(d,l)
				BL.extend(FR)
				for ll in FR:
					[ii,jj,kk]=ll
					Vn[ii][jj][kk]=-T[i][1]*kronecker_delta(i,j)-1
	for i in range(r):
		for j in range(r):
			LVn=[]
			for k in range(r):
				l=[i,j,k]
				if l in BL:
					LVn.append(Vn[i][j][k])
				else:
					FR=FrobRecList(d,l)
					BL.extend(FR)
					LVn.append(n)
					for ll in FR:
						[ii,jj,kk]=ll
						Vn[ii][jj][kk]=n
					n+=1
	A=[[0 for j in range(n)] for i in range(r*r)]
	Ve=[]
	for i in range(r):
		for j in range(r):
			Ve.append(T[i][0]*T[j][0]*T[i][1]*T[j][1])
			for k in range(r):
				nn=Vn[i][j][k]
				if nn<0:
					Ve[-1]+=T[k][0]*(nn+1)
				else:
					A[r*i+j][nn]+=T[k][0]
	AA=[]
	VVe=[]
	for i in range(r*r):
		if A[i]!=[0 for j in range(n)]:
			VVe.append(Ve[i])
			AA.append(A[i][1:])		# [1:] is just to fix n=1
		elif Ve[i]!=0:	
			#print(i,A[i],Ve[i])
			return [[],[]]
	return [AA,VVe]

def prenormaliz(T):
	[A,V]=PreSystem(T)
	L=TypeToList(T)
	s='['
	for a in L[:-1]:
		s+=str(a)+','
	s+=str(L[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space '+str(len(A[0]))+'\n')
	f.write('inhom_equations '+str(len(A))+'\n')
	for i in range(len(A)):
		A[i].append(-V[i])
	s=''
	for l in A:
		for ll in l:
			s+=str(ll)+' '
		s+='\n'
	f.write(s)
	f.write('LatticePoints'+'\n')
	f.write('convert_equations'+'\n')
	f.write('nonnegative'+'\n')
	f.close()
	
	
################ Induction matrices ##########

def SquareCode(i,j,r):
	return i+r*j

def InductionLowPart(M,L,D,F):	
	r=len(M)
	FPdim = sum([i^2 for i in L])
	R=[FPdim/i for i in F]
	R.sort()
	V=[sum([M[t][D[t]][j] for t in range(r)]) for j in range(r)]
	s='['
	for a in L[:-1]:
		s+=str(a)+','
	s+=str(L[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space '+str((r-1)^2)+'\n')
	f.write('inhom_equations '+str(2*(r-1))+'\n')
	s=''
	for j in range(1,r):
		W=[0 for ii in range(1,r) for jj in range(1,r)]	
		for t in range(1,r):
			W[t-1+(r-1)*(j-1)]=1
		for w in W:
			s+=str(w)+' '
		s+=str(-V[j])+'\n'	
	for i in range(1,r):
		W=[0 for ii in range(1,r) for jj in range(1,r)]
		for t in range(1,r):
			W[i-1+(r-1)*(t-1)]=L[t]
		for w in W:
			s+=str(w)+' '
		s+=str(-R[r-i]+1)+'\n'		
	f.write(s)	
	f.write('LatticePoints'+'\n')
	f.write('convert_equations'+'\n')
	f.write('nonnegative'+'\n')
	f.close()

###################

# Axiom redundency checking anti-involution

'''
LF=[
[[1,0,0,0,0,0,0],[0,1,0,0,0,0,0],[0,0,1,0,0,0,0],[0,0,0,1,0,0,0],[0,0,0,0,1,0,0],[0,0,0,0,0,1,0],[0,0,0,0,0,0,1]],
[[0,1,0,0,0,0,0],[1,1,0,1,0,1,1],[0,0,1,0,1,1,1],[0,1,0,0,1,1,1],[0,0,1,1,1,1,1],[0,1,1,1,1,1,1],[0,1,1,1,1,1,1]],
[[0,0,1,0,0,0,0],[0,0,1,0,1,1,1],[1,1,1,0,0,1,1],[0,0,0,1,1,1,1],[0,1,0,1,1,1,1],[0,1,1,1,1,1,1],[0,1,1,1,1,1,1]],
[[0,0,0,1,0,0,0],[0,1,0,0,1,1,1],[0,0,0,1,1,1,1],[1,0,1,1,0,1,1],[0,1,1,0,1,1,1],[0,1,1,1,1,1,1],[0,1,1,1,1,1,1]],
[[0,0,0,0,1,0,0],[0,0,1,1,1,1,1],[0,1,0,1,1,1,1],[0,1,1,0,1,1,1],[1,1,1,1,1,1,1],[0,1,1,1,1,2,1],[0,1,1,1,1,1,2]],
[[0,0,0,0,0,1,0],[0,1,1,1,1,1,1],[0,1,1,1,1,1,1],[0,1,1,1,1,1,1],[0,1,1,1,1,2,1],[0,1,1,1,1,0,4],[1,1,1,1,2,3,0]],
[[0,0,0,0,0,0,1],[0,1,1,1,1,1,1],[0,1,1,1,1,1,1],[0,1,1,1,1,1,1],[0,1,1,1,1,1,2],[1,1,1,1,2,3,0],[0,1,1,1,1,1,3]]
],[
[[1,0,0,0,0,0,0],[0,1,0,0,0,0,0],[0,0,1,0,0,0,0],[0,0,0,1,0,0,0],[0,0,0,0,1,0,0],[0,0,0,0,0,1,0],[0,0,0,0,0,0,1]],
[[0,1,0,0,0,0,0],[1,1,0,1,0,1,1],[0,0,1,0,1,1,1],[0,1,0,0,1,1,1],[0,0,1,1,1,1,1],[0,1,1,1,1,1,1],[0,1,1,1,1,1,1]],
[[0,0,1,0,0,0,0],[0,0,1,0,1,1,1],[1,1,1,0,0,1,1],[0,0,0,1,1,1,1],[0,1,0,1,1,1,1],[0,1,1,1,1,1,1],[0,1,1,1,1,1,1]],
[[0,0,0,1,0,0,0],[0,1,0,0,1,1,1],[0,0,0,1,1,1,1],[1,0,1,1,0,1,1],[0,1,1,0,1,1,1],[0,1,1,1,1,1,1],[0,1,1,1,1,1,1]],
[[0,0,0,0,1,0,0],[0,0,1,1,1,1,1],[0,1,0,1,1,1,1],[0,1,1,0,1,1,1],[1,1,1,1,1,1,1],[0,1,1,1,1,2,1],[0,1,1,1,1,1,2]],
[[0,0,0,0,0,1,0],[0,1,1,1,1,1,1],[0,1,1,1,1,1,1],[0,1,1,1,1,1,1],[0,1,1,1,1,2,1],[0,1,1,1,1,1,3],[1,1,1,1,2,2,1]],
[[0,0,0,0,0,0,1],[0,1,1,1,1,1,1],[0,1,1,1,1,1,1],[0,1,1,1,1,1,1],[0,1,1,1,1,1,2],[1,1,1,1,2,2,1],[0,1,1,1,1,2,2]]
]
sage: Axioms(LF[0])
[5, 5, 5]
False
sage: Axioms(LF[1])
[5, 5, 5]
False
'''

def HalfListToFusion(LL,L,d):
	mat=HalfMakemat(L,d)
	BL=[]; ISOM=[]
	T=ListToType(L)
	for l in LL:
		M=mat(l)
		if not M in ISOM:
			print(M)
			BL.append(M)
			ISOM.extend(isomorphicclass(M,T,d))
	return BL

def HalfMakemat(L,d):
	[var,M]=HalfSystem(L,d,1)
	r=len(M)
	def mat(l):
		N=[]
		for i in range(r):
			NN=[]
			for j in range(r):
				NNN=[]
				for k in range(r):
					x=M[i][j][k]
					if x in [0,1]:
						NNN.append(x)
					else:
						n=VarToIndex(x)
						NNN.append(l[n-1])
				NN.append(NNN)
			N.append(NN)
		return N
	return mat

def HalfTypesToNormaliz(LT):
	for T in LT:
		print(T)
		HalfTypeToNormaliz(T)

def HalfTypeToNormaliz(T):
	Du=duality(T)
	L=TypeToList(T)
	for d in Du:
		Halfnormaliz(L,d)

def Halfnormaliz(L,d):
	[A,V,M,Assoc]=HalfSystem(L,d,0)
	s='['
	for i in L[:-1]:
		s+=str(i)+','
	s+=str(L[-1])+']['
	for i in d[:-1]:
		s+=str(i)+','
	s+=str(d[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space '+str(len(A[0]))+'\n')
	f.write('inhom_equations '+str(len(A))+'\n')
	for i in range(len(A)):
		A[i].append(-V[i])
	s=''
	for l in A:
		for ll in l:
			s+=str(ll)+' '
		s+='\n'
	f.write(s)
	f.write('LatticePoints'+'\n')
	f.write('convert_equations'+'\n')
	f.write('nonnegative'+'\n')
	f.write('polynomial_equations '+str(len(Assoc))+'\n')
	s=''
	for As in Assoc:
		li=list(str(As))
		j=0
		for i in li:
			if i==str(x):
				s+='x['
				j=1
			elif j==1 and i in {' ','*','^'}:
				s+=']'+i
				j=0
			else:
				s+=i
		if j==1:
			s+='];\n'
		else:
			s+=';\n'
	f.write(s)
	f.close()

def HalfSystem(L,d,out):
	r=len(L)
	n=1		# Warning: need to put n=1 for the variables CoCoaLib version x[1], x[2], ..., but need n=0 for AA
	BL=[]
	V=[[[[] for k in range(r)] for j in range(r)] for i in range(r)]
	Vn=[[[[] for k in range(r)] for j in range(r)] for i in range(r)]
	vvar=[]
	for i in range(r):
		for j in range(r):
			l=[0,i,j]
			if not l in BL:
				FR=HalfFrobRecList(d,l)
				BL.extend(FR)
				for ll in FR:
					[ii,jj,kk]=ll
					V[ii][jj][kk]=kronecker_delta(i,j)
					Vn[ii][jj][kk]=kronecker_delta(i,j)-2
	for i in range(r):
		for j in range(r):
			LVn=[]
			for k in range(r):
				l=[i,j,k]
				if l in BL:
					LVn.append(Vn[i][j][k])
				else:
					FR=HalfFrobRecList(d,l)
					BL.extend(FR)
					v=var('x%d' % n)
					vvar.append(v)
					LVn.append(n)
					for ll in FR:
						[ii,jj,kk]=ll
						V[ii][jj][kk]=v
						Vn[ii][jj][kk]=n
					n+=1
	if out==0:				
		A=[[0 for j in range(n)] for i in range(r*r)]
		Ve=[]
		for i in range(r):
			for j in range(r):
				Ve.append(L[i]*L[j])
				for k in range(r):
					nn=Vn[i][j][k]
					if nn<0:
						nn+=2
						Ve[-1]-=L[k]*nn
					else:
						A[r*i+j][nn]+=L[k]
		AA=[]
		VVe=[]
		for i in range(r*r):
			if A[i]!=[0 for j in range(n)]:
				VVe.append(Ve[i])
				AA.append(A[i][1:])		# [1:] is just to fix n=1
			elif Ve[i]!=0:	
				return [[],[],[],[]]
		Assoc=[]
		for i in range(r):
			for j in range(r):
				for k in range(r):
					for t in range(r):
						eq=sum([V[i][j][s] * V[s][k][t] for s in range(r)]) - sum([V[j][k][s] * V[i][s][t] for s in range(r)])
						if eq!=0:
							Assoc.append(eq)		
	if out==0:
		return [AA,VVe,V,set(Assoc)]
	if out==1:
		return [vvar,V]
		



def HalfFrobRecList(d,l):
	[i,j,k]=l
	FR=[]
	T=[[i,j,k],[j,d[k],d[i]],[d[k],i,d[j]]]
	for t in T:
		if not t in FR:
			FR.append(t)
	FR.sort()
	return FR



######## For the modular case, containing the 12-term Frobenius reciprocity (thanks to commutativity)		# convention: 0 -> -1 for the duality

def DoubleListToFusion(LL,L,d):
	mat=DoubleMakemat(L,d)
	BL=[]; ISOM=[]
	T=ListToType(L)
	for l in LL:
		M=mat(l)
		if not M in ISOM:
			print(M)
			BL.append(M)
			ISOM.extend(isomorphicclass(M,T,d))
	return BL

def DoubleMakemat(L,d):
	[var,M]=DoubleSystem(L,d,1)
	r=len(M)
	def mat(l):
		N=[]
		for i in range(r):
			NN=[]
			for j in range(r):
				NNN=[]
				for k in range(r):
					x=M[i][j][k]
					if x in [0,1]:
						NNN.append(x)
					else:
						n=VarToIndex(x)
						NNN.append(l[n-1])
				NN.append(NNN)
			N.append(NN)
		return N
	return mat
	

def DoubleTypesToNormaliz(LT):
	for T in LT:
		print(T)
		DoubleTypeToNormaliz(T)

def DoubleTypesToPreNormaliz(LT):
	for T in LT:
		print(T)
		Doubleprenormaliz(T)

def DoubleTypeToNormaliz(T):
	Du=duality(T)
	L=TypeToList(T)
	for d in Du:
		Doublenormaliz(L,d)

def Doublenormaliz(L,d):
	[A,V,M,Assoc]=DoubleSystem(L,d,0)
	s='['
	for i in L[:-1]:
		s+=str(i)+','
	s+=str(L[-1])+']['
	s+=str(-1)+','
	for i in d[1:-1]:			# convention -1 in commutative case
		s+=str(i)+','
	s+=str(d[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space '+str(len(A[0]))+'\n')
	f.write('inhom_equations '+str(len(A))+'\n')
	for i in range(len(A)):
		A[i].append(-V[i])
	s=''
	for l in A:
		for ll in l:
			s+=str(ll)+' '
		s+='\n'
	f.write(s)
	f.write('LatticePoints'+'\n')
	f.write('convert_equations'+'\n')
	f.write('nonnegative'+'\n')
	f.write('polynomial_equations '+str(len(Assoc))+'\n')
	s=''
	for As in Assoc:
		li=list(str(As))
		j=0
		for i in li:
			if i==str(x):
				s+='x['
				j=1
			elif j==1 and i in {' ','*','^'}:
				s+=']'+i
				j=0
			else:
				s+=i
		if j==1:
			s+='];\n'
		else:
			s+=';\n'
	f.write(s)
	f.close()

def DoubleSystem(L,d,out):
	r=len(L)
	n=1		# Warning: need to put n=1 for the variables CoCoaLib version x[1], x[2], ..., but need n=0 for AA
	BL=[]
	V=[[[[] for k in range(r)] for j in range(r)] for i in range(r)]
	Vn=[[[[] for k in range(r)] for j in range(r)] for i in range(r)]
	vvar=[]
	for i in range(r):
		for j in range(r):
			l=[0,i,j]
			if not l in BL:
				FR=DoubleFrobRecList(d,l)
				BL.extend(FR)
				for ll in FR:
					[ii,jj,kk]=ll
					V[ii][jj][kk]=kronecker_delta(i,j)
					Vn[ii][jj][kk]=kronecker_delta(i,j)-2
	for i in range(r):
		for j in range(r):
			LVn=[]
			for k in range(r):
				l=[i,j,k]
				if l in BL:
					LVn.append(Vn[i][j][k])
				else:
					FR=DoubleFrobRecList(d,l)
					BL.extend(FR)
					v=var('x%d' % n)
					vvar.append(v)
					LVn.append(n)
					for ll in FR:
						[ii,jj,kk]=ll
						V[ii][jj][kk]=v
						Vn[ii][jj][kk]=n
					n+=1
	if out==0:				
		A=[[0 for j in range(n)] for i in range(r*r)]
		Ve=[]
		for i in range(r):
			for j in range(r):
				Ve.append(L[i]*L[j])
				for k in range(r):
					nn=Vn[i][j][k]
					if nn<0:
						nn+=2
						Ve[-1]-=L[k]*nn
					else:
						A[r*i+j][nn]+=L[k]
		AA=[]
		VVe=[]
		for i in range(r*r):
			if A[i]!=[0 for j in range(n)]:
				VVe.append(Ve[i])
				AA.append(A[i][1:])		# [1:] is just to fix n=1
			elif Ve[i]!=0:	
				return [[],[],[],[]]
		Assoc=[]
		for i in range(r):
			for j in range(i,r):
				for k in range(j,r):	# reduction of the associativity in the commutative case
					for t in range(r):
						eq1=sum([V[i][j][s] * V[s][k][t] for s in range(r)]) - sum([V[j][k][s] * V[i][s][t] for s in range(r)])
						eq2=sum([V[j][i][s] * V[s][k][t] for s in range(r)]) - sum([V[i][k][s] * V[j][s][t] for s in range(r)])
						if eq1!=0:
							Assoc.append(eq1)
						if eq2!=0:
							Assoc.append(eq2)	
	if out==0:
		return [AA,VVe,V,set(Assoc)]
	if out==1:
		return [vvar,V]

def DoubleFrobRecList(d,l):
	[i,j,k]=l
	FR=[]
	T=[[i,j,k],[d[i],k,j],[j,d[k],d[i]],[d[j],d[i],d[k]],[d[k],i,d[j]],[k,d[j],i],[j,i,k],[k,d[i],j],[d[k],j,d[i]],[d[i],d[j],d[k]],[i,d[k],d[j]],[d[j],k,i]]
	for t in T:
		if not t in FR:
			FR.append(t)
	FR.sort()
	return FR


def DoublePreSystem(T):	# dimension partition		# Warning: for the non-perfect the type should be written as [[1,1],[1,n],...]
	r=len(T)
	n=1		# Warning: need to put n=1 for the variables CoCoaLib version x[1], x[2], ..., but need n=0 for AA
	BL=[]
	Vn=[[[[] for k in range(r)] for j in range(r)] for i in range(r)]
	d=list(range(r))
	for i in range(r):
		for j in range(r):
			l=[0,i,j]
			if not l in BL:
				FR=DoubleFrobRecList(d,l)
				BL.extend(FR)
				for ll in FR:
					[ii,jj,kk]=ll
					Vn[ii][jj][kk]=-T[i][1]*kronecker_delta(i,j)-1
	for i in range(r):
		for j in range(r):
			LVn=[]
			for k in range(r):
				l=[i,j,k]
				if l in BL:
					LVn.append(Vn[i][j][k])
				else:
					FR=DoubleFrobRecList(d,l)
					BL.extend(FR)
					LVn.append(n)
					for ll in FR:
						[ii,jj,kk]=ll
						Vn[ii][jj][kk]=n
					n+=1
	A=[[0 for j in range(n)] for i in range(r*r)]
	Ve=[]
	for i in range(r):
		for j in range(r):
			Ve.append(T[i][0]*T[j][0]*T[i][1]*T[j][1])
			for k in range(r):
				nn=Vn[i][j][k]
				if nn<0:
					Ve[-1]+=T[k][0]*(nn+1)
				else:
					A[r*i+j][nn]+=T[k][0]
	AA=[]
	VVe=[]
	for i in range(r*r):
		if A[i]!=[0 for j in range(n)]:
			VVe.append(Ve[i])
			AA.append(A[i][1:])		# [1:] is just to fix n=1
		elif Ve[i]!=0:	
			#print(i,A[i],Ve[i])
			return [[],[]]
	return [AA,VVe]

def Doubleprenormaliz(T):
	[A,V]=DoublePreSystem(T)
	L=TypeToList(T)
	s='['
	for a in L[:-1]:
		s+=str(a)+','
	s+=str(L[-1])+']'
	f=open(s+'.in','w')
	f.write('amb_space '+str(len(A[0]))+'\n')
	f.write('inhom_equations '+str(len(A))+'\n')
	for i in range(len(A)):
		A[i].append(-V[i])
	s=''
	for l in A:
		for ll in l:
			s+=str(ll)+' '
		s+='\n'
	f.write(s)
	f.write('LatticePoints'+'\n')
	f.write('convert_equations'+'\n')
	f.write('nonnegative'+'\n')
	f.close()
