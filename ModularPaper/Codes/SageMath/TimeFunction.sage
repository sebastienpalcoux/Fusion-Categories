# %attach Nutstore/1/SAGE/TimeFunction.sage

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