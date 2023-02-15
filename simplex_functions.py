'''
plex(x,n)=x_n=x**n/fact(n)
proot=(lambda x,n: (x*fact(n))**(1/n))
(a+b)**n=sum(map(lambda k: choose(n,k)*a**k*b**(n-k),range(n+1)))
(a+b)_n=sum(map(lambda k: a_k*b_(n-k),range(n+1)))
lim_{n->∞} (choose(n,k)/n_k)=1 for all k (with equality at n=1 for integer k>1)
d(lambda x: x_n)=(lambda x: x_(n-1)), ∫(lambda x: x_n)=(lambda x: x_(n+1)),
d(lambda x: proot(x,n))=(lambda x: proot(x,n)/(x*n)), ∫(lambda x: proot(x,n))=(lambda x: proot(x,n)*x*n/(n+1)) (the same as with regular root function)
'''
from functools import reduce
from itertools import starmap,accumulate,groupby,product,combinations,chain,pairwise,zip_longest
from math import isqrt,lcm,floor,ceil,log,exp,factorial,gamma,inf #no ilog :-(
from scipy.special import polygamma#digamma
from fractions import Fraction
from operator import __add__,__mul__,__truediv__,__neg__
dot=(lambda a,b: sum(map(__mul__,a,b)))
ceilsqrt=(lambda x: (lambda s: s+(s**2<x))(isqrt(x)))
A007814=(lambda n: (~n&n-1).bit_length()) #thank you Chai Wah Wu
eulerMascheroni=0.577215664901532860606512090082402431042159335939923598805767234884867726777 #and so on
eulerEuler=exp(-eulerMascheroni) #this Euler fellow seems pretty good at maths
error=2**-8 #do not use for rocket science or anything
#n=2048
#eulerMascheroni=sum(map(lambda i: 1/i,range(1,n+1)))-log(n)
#eulerMascheroni=(lambda h: log(exp(h+1/n)-exp(h)))(sum(map(lambda i: 1/i,range(1,n)))) #thank you Richard R. Forberg

dbg=(lambda x,*s: (x,print(*s,x))[0]) #debug
lap=(lambda func,*iterables: list(map(func,*iterables)))
tap=(lambda func,*iterables: tuple(map(func,*iterables)))
larmap=(lambda func,iterable: list(starmap(func,iterable)))
tarmap=(lambda func,iterable: tuple(starmap(func,iterable)))
redumulate=(lambda f,l,i=None: accumulate(l,f,initial=i))
construce=(lambda f,l,i=None: reduce(lambda a,b: f(*a,b),l,i))
funcxp=(lambda f,l: lambda i: reduce(lambda x,i: f(x),range(l),i))
consxp=(lambda f,l: lambda i: reduce(lambda x,i: f(*x),range(l),i))
expumulate=(lambda f,l: lambda i: accumulate(range(l),lambda x,i: f(x),initial=i))

moddiv=(lambda a,b: divmod(a,b)[::-1])
fact=(lambda n: factorial(n) if type(n)==int else gamma(n+1))#(lambda n: reduce(int.__mul__,range(1,n+1)) if n else 1)
#difact=(lambda n: digamma(n+1))
polyfact=(lambda n,b=0: polygamma(b,n+1))
dact=(lambda n: fact(n)*polyfact(n))
#binomial=(lambda n,k: fact(n)//(fact(k)*fact(n-k)) if 0<=k<=n else 0)
choose=(lambda n,*k: (lambda n,*k: fact(n)//reduce(int.__mul__,map(fact,k)) if all(map(lambda k: 0<=k,k)) else 0)(n,*k,n-sum(k)))
def ilog(n,b):
    if b==1:
        return(inf)
    else:
        i=0
        while n>1:
            n//=b
            i+=1
        return(i-(not n))
#from https://mathoverflow.net/a/306972 (thank you user113386)
invfact=(lambda x: 0 if x==1 else (lambda t: t+ilog(x//fact(t),t+1))(A007814(x))) #requires input to be a factorial

plex=(lambda x,n: x**n/fact(n)) #x_n
proot=(lambda x,n: (x*fact(n))**(1/n)) #proot(x,n)_n=proot(x_n,n)=x

def plogmax(x): #finds point at which d(x**n/fact(n))/dn=0 by Newton's method as well #nonnegative function for our purposes so begins at 0
    #x**n*(log(x)-polyfact(n))/fact(n)=0
    #d(x**n*(log(x)-polyfact(n))/fact(n))/dn
    #=x**n*(-2*polyfact(n)*log(x)-polyfact(n,1)+log(x)**2+polyfact(n)**2)/fact(n)
    #=x**n*((polyfact(n)-log(x))**2-polyfact(n,1))/fact(n)
    #n'=n+(0-d(x**n/fact(n))/dn)/(d(d(x**n/fact(n))/dn)/dn)
    #n+=(x**n*(polyfact(n)-log(x))/fact(n))/(x**n*((polyfact(n)-log(x))**2-polyfact(n,1))/fact(n))
    #n+=(lambda p: (x**n*p/fact(n))/(x**n*(p**2-polyfact(n,1))/fact(n)))(polyfact(n)-log(x))
    if x>=eulerEuler: #it is asymptotic to n=x but is nonnegative (for our purposes), plogmax will be negative in such cases
        n=x
        d=1
        while abs(d)>error:
            d=(lambda p: 1/(p-polyfact(n,1)/p))(polyfact(n)-log(x))
            n+=d
        return(n)
    else:
        return(0)

def plog(o,x,principal=True): #solve x**n/fact(n)=o for n (returns two positive roots if possible, Newton's method) #princ
    p=plogmax(x)
    m=x**p/fact(p)
    if o>m:
        raise(ValueError("no length-"+str(x)+" simplex has a hypervolume of "+str(o)+" (maximum "+str(m)+" at n="+str(p)+") :-("))
    # d(x**n/fact(n))/dn
    #=d(x**n*fact(n)**-1)/dn
    #=d(x**n)/dn*fact(n)**-1+x**n*(fact(n)**-1)/dn
    #=log(x)*x**n/fact(n)+x**n*(fact(n)**-1)/d(fact(n))*d(fact(n))/dn
    #=x**n*(log(x)/fact(n)+(fact(n)**-1)/d(fact(n))*d(fact(n))/dn)
    #=x**n*(log(x)/fact(n)-fact(n)**-2*dact(n))
    #=x**n*(log(x)/fact(n)-fact(n)**-2*fact(n)*polyfact(n))
    #=x**n*(log(x)-polyfact(n))/fact(n)
    #n'=n+(o-x**n/fact(n))/d(x**n/fact(n))/dn
    #  =n+(o-x**n/fact(n))/(x**n*(log(x)-polyfact(n))/fact(n))
    #  =n+(fact(n)*o/x**n-1)/(log(x)-polyfact(n))
    def newton(n):
        d=1
        while abs(d)>error:
            d=(fact(n)*o/x**n-1)/(log(x)-polyfact(n))
            #print(d)
            #der=(o-x**n/fact(n))/((x**(n+error)/fact(n+error)-x**n/fact(n))/error)#print(n,d,der)
            n+=d
        return(n)
    if principal:
        return(1.0 if o==x else newton(0))
    else:
        output=(newton(p+1),) #initial approximation (upper bound)
        if p>0 and 1<o<m:
            output+=(1.0 if o==x else newton(0),)
        return(output)

#print(tap(lambda n: invfact(fact(n)),range(8)))
#print(tap(invfact,range(16)))

#print(plog(6,2))
print(plog(2.1,2))
print(plog(1.5,2))

print(plog(2,4),plog(3,4),plog(6,4))

print(plog(6,4)/(plog(2,4)+plog(3,4)))

choosopoly=(lambda k: (reduce(lambda a,k: tarmap(lambda a,b: a-k*b,pairwise((0,)+a+(0,))),range(k),(1,)),fact(k))) #choose(n,k)=(lambda k: sum(map(lambda i: __pow__(n,i),k[0]))/k[1])(choosopoly(k))

def exchange(a,i,j):
    a[i],a[j]=a[j],a[i]
    return(a)

inverse=(lambda a,f=True: tap(lambda i: i[len(i)//2:],(lambda a: reduce(lambda a,i: (lambda a: larmap(lambda j,c: (lambda i,j,column,target=0: tap(lambda c,d: d-(Fraction if f else __truediv__)((j[column]-target)*c,i[column]),i,j))(a[i],c,i,j==i),enumerate(a)))(a if a[i][i] else exchange(a,i,next(filter(lambda j: a[i][j]!=0,range(i+1,len(a)))))),range(len(a)),a))(larmap(lambda i,row: row+(0,)*i+(1,)+(0,)*(len(a)+~i),enumerate(a))))) #Gaussian elimination
choosatrix=(lambda k,d=True: tap(lambda j: (lambda c: tap(lambda n: Fraction(n,c[1]) if d else n,c[0])+(Fraction(0,1),)*(k+~j))(choosopoly(j)),range(k))) #find correct assemblage of chooses to compute x**k (construct k-hypercube out of ceiling-simplexes)
fratrix=(lambda m,dims=2,strict=True: (lambda m: '\n'.join((lambda s: (lambda c: starmap(lambda i,r: (' ' if i else '(')+(','+'\n'*(dims==3)).join(starmap(lambda i,s: ' '*(c[i]-len(s))+s,enumerate(r)))+(',' if len(m)+~i else ')'),enumerate(s)))(tap(lambda c: max(map(len,c)),zip(*s))))(tap(lambda r: tap(lambda f: fratrix(f,2,strict) if dims==3 else str(f.numerator)+('/'+str(f.denominator))*(f.denominator!=1) if type(f)==Fraction else str(f),r),m))))(m if dims==2 else (m,)))
print(fratrix(choosatrix(8,False)))
print(fratrix(choosatrix(8)))
print(fratrix(tap(lambda r: tarmap(lambda i,c: c*fact(i),enumerate(r)),choosatrix(8))))
print(fratrix(tap(lambda r: tarmap(lambda i,c: c*fact(i),enumerate(r)),choosatrix(8,False))))
powtrix=(lambda k: inverse(choosatrix(k)))#=tarmap(lambda i,r: tap(lambda c: c*fact(i),r),enumerate(inverse(tap(lambda r: tarmap(lambda i,c: c*fact(i),enumerate(r)),choosatrix(8)))))
print(fratrix(powtrix(8)))
#print(fratrix(inverse(tap(lambda r: tarmap(lambda i,c: c*fact(i),enumerate(r)),choosatrix(8)))))

binomiator=(lambda n,o: tap(lambda k: choose(n,k)*o**(n-k),range(n+1))) #expands (x+o)**n as polynomial over n
flatten=(lambda m: reduce(lambda a,b: tap(__add__,a,b),m) if m else m)
offset=(lambda p,o: flatten(tarmap(lambda i,n: tap(lambda b: n*b,binomiator(i,o))+(0,)*(len(p)+~i),enumerate(p))))
#recurrence=(lambda p: inverse(tap(lambda o: offset(p,o),range(-1,~len(p),-1)))) #for polynomials in particular
#recurrence=(lambda p: flatten(tap(lambda r: dot(r,p),inverse(tap(lambda o: offset(p,o),range(-1,~len(p),-1)))))) #for polynomials in particular
recurrence=(lambda p: tap(lambda r: dot(r,p),inverse(tuple(zip(*tap(lambda o: offset(p,o),range(-1,~len(p),-1))))))) #for polynomials in particular
multicurrence=(lambda m: (lambda l: tap(lambda r: dot(r,reduce(tuple.__add__,tarmap(lambda f,p: f(0,p),m))),inverse(reduce(tuple.__add__,starmap(lambda f,p: tuple(zip(*tap(lambda o: offset(f(o,p),o),range(-1,~l,-1)))),m)))))(sum(starmap(lambda f,p: len(p),m)))) #polynomials in multiple variables
polyst=(lambda o,x='x': ''.join(starmap(lambda j,t: (lambda j,i,t: '+'*(j and t>=0)+str(t)+(('*'+x if i==1 else '*'+x+'**'+str(i)) if i else ''))(j,*t),enumerate(filter(lambda t: t[1],enumerate(o))))))
recurquation=(lambda p,l=True,v=False: (lambda r: 'a=(lambda x: '*l+polyst(p)+'), a(x)'*l+'='+''.join(starmap(lambda j,c: '+'*(j and c>=0)+str(c)+'*'+(lambda s: 'a'+s if l else '('+polyst(p,s)+')')('(x-'+str(j+1)+')'),enumerate(r)))+('='+'+'.join(starmap(lambda o,c: '('+polyst(tap(lambda t: c*t,offset(p,~o)))+')',enumerate(r))) if v else ''))(recurrence(p)))
print(fratrix((lambda p: (tap(lambda o: offset(p,o),range(-1,~len(p),-1))))((0,2,3))))
print(fratrix((lambda p: inverse(tap(lambda o: offset(p,o),range(-1,~len(p),-1))))((0,2,3))))
#A357723 :-)
print(fratrix(multicurrence(((lambda i,p: p,(Fraction(1,4),Fraction(3,8),Fraction(-3,4),0,Fraction(1,8))),(lambda i,p: tap(lambda x: x*(-1)**-i,p),(Fraction(1,4),Fraction(3,8),Fraction(-1,8))))),1))
#A358339 ',:-)
print(recurquation((-1,Fraction(-1,2),Fraction(1,2))))
print(recurquation((-1,Fraction(-1,2),-1,Fraction(1,2))))
print(recurquation((6,-7,2)))
print(recurquation((12,25,13,1),True))
print(fratrix(multicurrence(((lambda i,p: p,(Fraction(-5,4),Fraction(83,24),Fraction(-29,6),Fraction(91,24),Fraction(-25,24),Fraction(-5,4),Fraction(1,8))),(lambda i,p: tap(lambda x: x*(-1)**-i,p),(Fraction(1,4),Fraction(-11,24),Fraction(1,4),Fraction(-1,24))))),1))

leadcurrence=(lambda p: (lambda i: recurrence(p[:-i] if i else p)+(0,)*i)(next(filter(lambda p: p[1],enumerate(p[::-1])))[0]))
print(fratrix(tap(lambda p: (1,)+tap(__neg__,leadcurrence(p)),choosatrix(8))))

multicurrence(((lambda i,p: p,(1,)*3),(lambda i,p: tap(lambda x: x*(-1)**-i,p),(1,)*2)))
print(fratrix(tap(lambda n: tap(lambda k: multicurrence(((lambda i,p: p,(1,)*n),(lambda i,p: tap(lambda x: x*(-1)**-i,p),(1,)*k)))+(0,)*(n-k),range(n+1)),range(8)),3))
print(fratrix(tap(lambda n: tap(lambda k: multicurrence(((lambda i,p: p,(1,)*n),(lambda i,p: tap(lambda x: x*(-1)**-i,p),(1,)*k))),range(n+1)),range(8)),3,False))
