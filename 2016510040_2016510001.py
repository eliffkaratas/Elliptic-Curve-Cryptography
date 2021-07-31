from tkinter import *
import collections
import numpy as np
import time
# generate random integer values
from random import seed
from random import randint

def isPrime(x):
    """checking prime number"""
    count = 0
    for i in range(int(x/2)):
        if x % (i+1) == 0:
            count = count+1
    return count == 1

def getRandomPrimeInteger(bounds):
    """getting random prime number for EC"""
    for i in range(bounds.__len__()-1):
        if bounds[i + 1] > bounds[i]:
            x = bounds[i] + np.random.randint(bounds[i+1]-bounds[i])
            if isPrime(x):
                return x

        else:
            if isPrime(bounds[i]):
                return bounds[i]

        if isPrime(bounds[i + 1]):
            return bounds[i + 1]

    newBounds = [0 for i in range(2*bounds.__len__() - 1)]
    newBounds[0] = bounds[0]
    for i in range(1, bounds.__len__()):
        newBounds[2*i-1] = int((bounds[i-1] + bounds[i])/2)
        newBounds[2*i] = bounds[i]

    return getRandomPrimeInteger(newBounds)

# Upper bound for prime number is 250. It can be changed.
upperBound = 250        
bounds = [3, upperBound]
num = getRandomPrimeInteger(bounds)

def inv(n, q):
    """div on PN modulo a/b mod q as a * inv(b, q) mod q
    >>> assert n * inv(n, q) % q == 1
    """
    # n*inv % q = 1 => n*inv = q*m + 1 => n*inv + q*-m = 1
    # => egcd(n, q) = (inv, -m, 1) => inv = egcd(n, q)[0] (mod q)
    return egcd(n, q)[0] % q
    #[ref] naive implementation
    #for i in range(q):
    #    if (n * i) % q == 1:
    #        return i
    #    pass
    #assert False, "unreached"
    #pass


def egcd(a, b):
    """extended GCD
    returns: (s, t, gcd) as a*s + b*t == gcd
    >>> s, t, gcd = egcd(a, b)
    >>> assert a % gcd == 0 and b % gcd == 0
    >>> assert a * s + b * t == gcd
    """
    s0, s1, t0, t1 = 1, 0, 0, 1
    while b > 0:
        q, r = divmod(a, b)
        a, b = b, r
        s0, s1, t0, t1 = s1, s0 - q * s1, t1, t0 - q * t1
        pass
    return s0, t0, a


def sqrt(n, q):
    """sqrt on PN modulo: returns two numbers or exception if not exist
    >>> assert (sqrt(n, q)[0] ** 2) % q == n
    >>> assert (sqrt(n, q)[1] ** 2) % q == n
    """
    assert n < q
    for i in range(1, q):
        if i * i % q == n:
            return (i, q - i)
        pass
    raise Exception("not found")


Coord = collections.namedtuple("Coord", ["x", "y"])

class EC(object):
    """System of Elliptic Curve"""
    def __init__(self, a, b, q):
        """elliptic curve as: (y**2 = x**3 + a * x + b) mod q
        - a, b: params of curve formula
        - q: prime number
        """
        assert 0 < a and a < q and 0 < b and b < q and q > 2
        assert (4 * (a ** 3) + 27 * (b ** 2))  % q != 0
        self.a = a
        self.b = b
        self.q = q
        # just as unique ZERO value representation for "add": (not on curve)
        self.zero = Coord(0, 0)
        pass

    def is_valid(self, p):
        if p == self.zero: return True
        l = (p.y ** 2) % self.q
        r = ((p.x ** 3) + self.a * p.x + self.b) % self.q
        return l == r

    def at(self, x):
        """find points on curve at x
        - x: int < q
        - returns: ((x, y), (x,-y)) or not found exception
        >>> a, ma = ec.at(x)
        >>> assert a.x == ma.x and a.x == x
        >>> assert a.x == ma.x and a.x == x
        >>> assert ec.neg(a) == ma
        >>> assert ec.is_valid(a) and ec.is_valid(ma)
        """
        assert x < self.q
        ysq = (x ** 3 + self.a * x + self.b) % self.q
        y, my = sqrt(ysq, self.q)
        return Coord(x, y), Coord(x, my)

    def neg(self, p):
        """negate p
        assert ec.is_valid(ec.neg(p))
        """
        return Coord(p.x, -p.y % self.q)

    def add(self, p1, p2):
        """<add> of elliptic curve: negate of 3rd cross point of (p1,p2) line
        >>> d = ec.add(a, b)
        >>> assert ec.is_valid(d)
        >>> assert ec.add(d, ec.neg(b)) == a
        >>> assert ec.add(a, ec.neg(a)) == ec.zero
        >>> assert ec.add(a, b) == ec.add(b, a)
        >>> assert ec.add(a, ec.add(b, c)) == ec.add(ec.add(a, b), c)
        """
        if p1 == self.zero: return p2
        if p2 == self.zero: return p1
        if p1.x == p2.x and (p1.y != p2.y or p1.y == 0):
            # p1 + -p1 == 0
            return self.zero
        if p1.x == p2.x:
            # p1 + p1: use tangent line of p1 as (p1,p1) line
            l = (3 * p1.x * p1.x + self.a) * inv(2 * p1.y, self.q) % self.q
            pass
        else:
            l = (p2.y - p1.y) * inv(p2.x - p1.x, self.q) % self.q
            pass
        x = (l * l - p1.x - p2.x) % self.q
        y = (l * (p1.x - x) - p1.y) % self.q
        return Coord(x, y)

    def mul(self, p, n):
        """n times <mul> of elliptic curve
        >>> m = ec.mul(p, n)
        >>> assert ec.is_valid(m)
        >>> assert ec.mul(p, 0) == ec.zero
        """
        r = self.zero
        m2 = p
        # O(log2(n)) add
        while 0 < n:
            if n & 1 == 1:
                r = self.add(r, m2)
                pass
            n, m2 = n >> 1, self.add(m2, m2)
            pass
        # [ref] O(n) add
        #for i in range(n):
        #    r = self.add(r, p)
        #    pass
        return r

    def order(self, g):
        """order of point g
        >>> o = ec.order(g)
        >>> assert ec.is_valid(a) and ec.mul(a, o) == ec.zero
        >>> assert o <= ec.q
        """
        assert self.is_valid(g) and g != self.zero
        for i in range(1, self.q + 1):
            if self.mul(g, i) == self.zero:
                return i
            pass
        raise Exception("Invalid order")
    pass

class ElGamal(object):
    """ElGamal Encryption
    pub key encryption as replacing (mulmod, powmod) to (ec.add, ec.mul)
    - ec: elliptic curve
    - g: (random) a point on ec
    """
    def __init__(self, ec, g):
        assert ec.is_valid(g)
        self.ec = ec
        self.g = g
        self.n = ec.order(g)
        pass

    def gen(self, priv):
        """generate pub key
        - priv: priv key as (random) int < ec.q
        - returns: pub key as points on ec
        """
        return self.ec.mul(g, priv)

    def enc(self, plain, pub, r):
        """encrypt
        - plain: data as a point on ec
        - pub: pub key as points on ec
        - r: random int < ec.q
        - returns: (cipher1, cipher2) as points on ec
        """
        assert self.ec.is_valid(plain)
        assert self.ec.is_valid(pub)
        return (self.ec.mul(g, r), self.ec.add(plain, self.ec.mul(pub, r)))

    def dec(self, cipher, priv):
        """decrypt
        - chiper: (chiper1, chiper2) as points on ec
        - priv: private key as int < ec.q
        - returns: plain as a point on ec
        """
        c1, c2 = cipher
        assert self.ec.is_valid(c1) and ec.is_valid(c2)
        return self.ec.add(c2, self.ec.neg(self.ec.mul(c1, priv)))
    pass

print("prime number:",num)

seed(1)
# a,b,priv,x, and r values must be smaller than prime number
a = randint(2, num)
b = randint(2, num)
priv = randint(2, num)
at = randint(2,num)
r = randint(2,num)

print("a:",a)
print("b:",b)
print("private key:",priv)
print("x:",at)
print("r:",r)

# For 1 time exc.

start_time1 = time.time()

ec = EC(a, b, num)
g, _ = ec.at(at)
assert ec.order(g) <= ec.q
            
# ElGamal enc/dec usage
eg = ElGamal(ec, g)
# mapping value to ec point
# "masking": value k to point ec.mul(g, k)
# ("imbedding" on proper n:use a point of x as 0 <= n*v <= x < n*(v+1) < q)
mapping = [ec.mul(g, i) for i in range(eg.n)]
plain = mapping[at]    
pub = eg.gen(priv)   
cipher = eg.enc(plain, pub, r) 
decoded = eg.dec(cipher, priv)
assert decoded == plain
assert cipher != pub

average_time1 = time.time() - start_time1


# For 1000 times exc.

start_time2 = time.time()
    
for i in range (1000):       
    ec = EC(a, b, num)
    g, _ = ec.at(at)
    assert ec.order(g) <= ec.q   
    # ElGamal enc/dec usage
    eg = ElGamal(ec, g)
    # mapping value to ec point
    # "masking": value k to point ec.mul(g, k)
    # ("imbedding" on proper n:use a point of x as 0 <= n*v <= x < n*(v+1) < q)
    mapping = [ec.mul(g, i) for i in range(eg.n)]
    plain = mapping[at] 
    pub = eg.gen(priv) 
    cipher = eg.enc(plain, pub, r)
    decoded = eg.dec(cipher, priv)  
    assert decoded == plain
    assert cipher != pub
    
average_time2 = (time.time() - start_time2) / 1000       

# Program GUI 
            
parent = Tk()
parent.title("Elliptic-Curve Cryptography with El-Gamal Encryption/Decryption")

parent.geometry("1100x440")
parent.configure(bg='white')

converted_num = str(num)
converted_a = str(a)
converted_b = str(b)
converted_priv = str(priv)
converted_at = str(at)
converted_r = str(r)
converted_pub = str(pub)
converted_plain=str(plain)
converted_cipher=str(cipher)
converted_decoded=str(decoded)
converted_average_time1=str(average_time1)
converted_average_time2=str(average_time2)

var_converted_num = StringVar()
var_converted_num .set(converted_num)

var_converted_a = StringVar()
var_converted_a .set(converted_a)

var_converted_b = StringVar()
var_converted_b .set(converted_b)

var_converted_priv = StringVar()
var_converted_priv .set(converted_priv)

var_converted_at = StringVar()
var_converted_at .set(converted_at)

var_converted_r = StringVar()
var_converted_r .set(converted_r)

var_converted_pub = StringVar()
var_converted_pub .set(converted_pub)

var_converted_plain = StringVar()
var_converted_plain .set(converted_plain)

var_converted_cipher = StringVar()
var_converted_cipher .set(converted_cipher)

var_converted_decoded = StringVar()
var_converted_decoded .set(converted_decoded)
                          
var_converted_average_time1 = StringVar()
var_converted_average_time1 .set(converted_average_time1)

var_converted_average_time2 = StringVar()
var_converted_average_time2 .set(converted_average_time2)

Label(parent, text="Prime number is",font = ('Arial', 12,'bold'),fg='blue',bg='white').grid(row=0, column=0, sticky="w")
Label(parent, textvariable=var_converted_num, font = ('Arial', 12),bg='white').grid(row=0, column=3, sticky="w")

Label(parent, text='Parameter a is',font = ('Arial', 12,'bold'),fg='blue',bg='white').grid(row=1, column=0, sticky="w")
Label(parent, textvariable=var_converted_a, font = ('Arial', 12),bg='white').grid(row=1, column=3, sticky="w")

Label(parent, text='Parameter b is',font = ('Arial', 12,'bold'),fg='blue',bg='white').grid(row=2, column=0, sticky="w")
Label(parent, textvariable=var_converted_b, font = ('Arial', 12),bg='white').grid(row=2, column=3, sticky="w")

Label(parent, text="Private key is",font = ('Arial', 12,'bold'),fg='blue',bg='white').grid(row=3, column=0, sticky="w")
Label(parent, textvariable=var_converted_priv, font = ('Arial', 12),bg='white').grid(row=3, column=3, sticky="w")

Label(parent, text="(Generating value of [(x ** 3 + .a * x + b) % (primenumber)] and g point to use in ElGamal encryption)",font = ('Arial', 12,'bold'),fg='blue',bg='white').grid(row=4, column=0, sticky="w")
Label(parent, text="Find points on curve at",font = ('Arial', 12,'bold'),fg='blue',bg='white').grid(row=5, column=0, sticky="w")
Label(parent, textvariable=var_converted_at, font = ('Arial', 12),bg='white').grid(row=5, column=3, sticky="w")

Label(parent, text="(Generating r point to use in EC mul. and ElGamal encryption)",font = ('Arial', 12,'bold'),fg='blue',bg='white').grid(row=6, column=0, sticky="w")
Label(parent, text="Point r on curve is",font = ('Arial', 12,'bold'),fg='blue',bg='white').grid(row=7, column=0, sticky="w")
Label(parent, textvariable=var_converted_r, font = ('Arial', 12),bg='white').grid(row=7, column=3, sticky="w")

Label(parent, text="Public key is",font = ('Arial', 12,'bold'),bg='white').grid(row=9, column=0, sticky="w")

Label(parent, text="Plain points on curve are",font = ('Arial', 12,'bold'),bg='white').grid(row=10, column=0, sticky="w")

Label(parent, text="Cipher points on curve are",font = ('Arial', 12,'bold'),bg='white').grid(row=11, column=0, sticky="w")

Label(parent, text="Decoded points on curve are",font = ('Arial', 12,'bold'),bg='white').grid(row=13, column=0, sticky="w")

Label(parent, text="",font = ('Arial', 12,'bold'),bg='white').grid(row=14, column=0, sticky="w")

Label(parent, text="Time for encrytion/decryption is",font = ('Arial', 12,'bold'),bg='white').grid(row=15, column=0, sticky="w")

Label(parent, text="Average time for 1000 times encryption/decryption is",font = ('Arial',12,'bold'),bg='white').grid(row=16, column=0, sticky="w")

def calculateEnc(): 
    Label(parent, textvariable=var_converted_pub,font = ('Arial', 12),bg='white').grid(row=9, column=3, sticky="w")      
    Label(parent, textvariable=var_converted_plain, font = ('Arial', 12),bg='white').grid(row=10, column=3, sticky="w") 
    Label(parent, textvariable=var_converted_cipher, font = ('Arial', 12),bg='white').grid(row=11, column=3, sticky="w") 

def calculateDec():  
    Label(parent, textvariable=var_converted_decoded, font = ('Arial', 12),bg='white').grid(row=13, column=3, sticky="w")
    Label(parent, textvariable=var_converted_average_time1, font = ('Arial', 12),bg='white').grid(row=15, column=3, sticky="w")
    Label(parent, textvariable=var_converted_average_time2, font = ('Arial', 12),bg='white').grid(row=16, column=3, sticky="w")
  
Button(parent, text='Encryption',font = ('Arial', 12,'bold'),fg='green',bg='white',command=calculateEnc).grid(row=8, column=3,sticky="w")
Button(parent, text='Decryption',font = ('Arial', 12,'bold'),fg='red',bg='white',command=calculateDec).grid(row=12, column=3,sticky="w")

parent.mainloop()


        
    
       

    
    
    



