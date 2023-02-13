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
ceilsqrt=(lambda x: (lambda s: s+(s**2<x))(isqrt(x)))
A007814=(lambda n: (~n&n-1).bit_length()) #thank you Chai Wah Wu
eulerMascheroni=0.577215664901532860606512090082402431042159335939923598805767234884867726777 #and so on
eulerEuler=exp(-eulerMascheroni) #this Euler fellow seems pretty good at maths
error=2**-8 #do not use for rocket science or anything
#n=2048
#eulerMascheroni=sum(map(lambda i: 1/i,range(1,n+1)))-log(n)
#eulerMascheroni=(lambda h: log(exp(h+1/n)-exp(h)))(sum(map(lambda i: 1/i,range(1,n)))) #thank you Richard R. Forberg

dbg=(lambda x,*s: (x,print(*s,x))[0]) #debug
tap=(lambda func,*iterables: tuple(map(func,*iterables)))
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
