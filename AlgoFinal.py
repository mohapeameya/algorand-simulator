import simpy, random, numpy as np, math
from ellipticcurve.ecdsa import Ecdsa
from ellipticcurve.privateKey import PrivateKey
import queue
import hashlib
from queue import PriorityQueue

N = 20
W = 0
genesis = "WE LOVE BTC"
blockflag = 0
Timeout = 0
GRAPH = {}
NODEMESSAGES = {}
DELAY = {}
LINKMESSAGES = {}
shas = {}
Incomingmsg = {} #reciever:msg
tau_proposer = 5
tau_step = 3

class MyPriorityQueue(PriorityQueue):
    def __init__(self):
        PriorityQueue.__init__(self)
        self.counter = 0

    def put(self, priority, item):
        PriorityQueue.put(self, (priority, self.counter, item))
        self.counter += 1

    def get(self, *args, **kwargs):
        _, _, item = PriorityQueue.get(self, *args, **kwargs)
        return item

gsp_list = list()
msgQueue = list()
for i in range(N):
    msgQueue.append(MyPriorityQueue())
    gsp_list.append(list())
# msgQueue = [MyPriorityQueue()] *N

for i in range(N):
    GRAPH[i] = []
    NODEMESSAGES[i] = []


def hashof(seed):
    '''
    :param seed: seed for hashing
    :return sha256 hash in hex:
    '''
    m = hashlib.sha256(str(seed).encode('utf-8')).hexdigest()
    return m


class NetworkMsg():
    counter = 0
    def __init__(self, message, sender, ts, type, round, step):
        self.message = message
        self.sentfrom = sender
        self.ts = ts
        self.type = type
        self.round = round
        self.step = step
        self.uid = NetworkMsg.counter
        NetworkMsg.counter += 1

    def setreciever(self, recv):
        self.receiver = recv

    def setDelay(self, delay):
        self.delay = delay

    def __str__(self):
        return str(self.message)


def main():
    env = simpy.Environment()
    for i in range(N):
        env.process(Nodes(env, i))
    env.run()
    print("Total stake: ", W)
    print("Simulation ends")


def combOpt(k, n, p):
    if k == 0:
        return 1
    if k>n:
        return 0
    if k*2 > n:
        k = n-k
        p = 1.0 - p
    result = n*p
    for i in range(2, k+1):
        result *= (n - i + 1)
        result /= i
        result *= p
    return result


def binomialOpt(k, w, p):
    combWx = combOpt(k, w, p)
    if k * 2 > w :
        pK=p**k
        return combWx * pK
    else:
        qWK = (1.0 - p)**(w - k)
        return combWx * qWK
    pass


def binomialsum(j, w, p):
    sum = 0
    for k in range(j+1):
        sum += binomialOpt(k, w, p)
    return sum


def PRG(seed):
    s = random
    s.seed(seed)
    return int(s.getrandbits(256)).to_bytes(32,"big")


def prove(message, sk):
    return Ecdsa.sign(message,sk)


def verify(publickey,hash,signature):
    return Ecdsa.verify(hash, signature, publickey)


def sortition(sk,seed, T, role, w , W):
    message = str(seed)+str(role)
    hashvalue = PRG(message)
    signature = prove(hashvalue, sk)
    p = T/W
    j = 0
    # (hashvalue,signature) = vrf
    hashInt = int.from_bytes(hashvalue, "big")
    value = hashInt / (2**(len(hashvalue)*8))
    # print("value in sortition: ", value)
    while (value < binomialsum(j, w, p) or value >= binomialsum(j + 1, w, p)) and binomialsum(j, w, p) != binomialsum(j+1, w, p):
        if binomialsum(j, w, p) > 1 or binomialsum(j + 1, w, p) > 1:
            break
        j += 1
    return hashvalue,signature,j


def verifySort(publickey,hashvalue,signature,T,w,W):
    p = T / W
    j = 0
    check = verify(publickey, hashvalue, signature)
    if check == False:
        return 0
    # (hashvalue, signature) = vrf
    hashInt = int.from_bytes(hashvalue, "big")
    value = hashInt / (2 ** (len(hashvalue) * 8))
    while (value < binomialsum(j, w, p) or value >= binomialsum(j + 1, w, p)) and binomialsum(j, w, p) != binomialsum(
            j + 1, w, p):
        if binomialsum(j, w, p) > 1 or binomialsum(j + 1, w, p) > 1:
            break
        j += 1
    return j


def createNetworkOverlay(id):
    m = random.randint(1, 3)
    delay = random.randint(70, 150)
    while m > 0:
        neighbour = random.randint(0, N-1)
        while neighbour == id:
            neighbour = random.randint(0, N-1)
        if len(GRAPH[neighbour]) > 4:
            continue
        if len(GRAPH[id]) > 6:
            break
        if neighbour not in GRAPH[id]:
            GRAPH[id].append(neighbour)
            DELAY[(id,neighbour)] = delay
            LINKMESSAGES[(id,neighbour)] = []
            if id not in GRAPH[neighbour]:
                GRAPH[neighbour].append(id)
                LINKMESSAGES[(neighbour,id)] = []
                DELAY[(neighbour, id)] = delay
            m -= 1


def sendmsg(id, msg, env):
    neighbours = GRAPH[id]
    # print_msglist()
    for n in neighbours:
        msg.setreciever(n)
        msg.setDelay(DELAY[(id, n)])
        delay = env.now + DELAY[(id,n)]
        msgQueue[n].put(delay, (delay, msg))
        print("Time: ", env.now, id, " Sendin to :", n, " of time: ", delay)
        # print(type(msgQueue))
        # print(type(msgQueue[n]))
        # print_msglist()

def recieve(id,env):
    msg = ""
    if msgQueue[id].empty() == False:
        delay,msg = msgQueue[id].get()
        return (delay,msg)

def print_msglist():
    for id, item in enumerate(msgQueue):
        print (id , " : ", item.queue)

def chk_dup(msg, id):
    if msg.uid not in gsp_list[id]:
        gsp_list[id].append(msg.uid)
        return True
    else:
        # print("Duplicate found")
        return False

def validate(self, payload, signature, ):
    return Ecdsa.verify(self.payload, self.sign, self.publicKey)


def Nodes(env, id):
    privateKey = PrivateKey()
    publicKey = privateKey.publicKey()
    w = random.randint(1, 50) #stake
    prevBlock = genesis
    global W
    W = W + w
    yield env.timeout(0)
    createNetworkOverlay(id)
    yield env.timeout(0)
    hashvalue, signature, j = sortition(privateKey, hashof(genesis), 5, "comittee", w, W)
    vrfhash = Ecdsa.sign(hashvalue, privateKey)  # signature on hash of prg is vrfhash
    LowestSHA = None
    round= 1
    if j > 0:
        Lowestpriorityj = 1
        print(id, "is a block proposer with sub-users =", j)
        for subuser in range(1, j + 1):
            m = hashlib.sha256()
            m.update((str(vrfhash) + str(subuser)).encode())
            newsha = int.from_bytes(m.digest(), 'big')
            if LowestSHA is None:
                LowestSHA = newsha
                Lowestpriorityj = subuser
            elif newsha < LowestSHA:
                LowestSHA = newsha
                Lowestpriorityj = subuser
        shas[id] = LowestSHA
        gossip = NetworkMsg(LowestSHA, id, env.now, "shacmpare", round, "step1")
        # gossip = str(round) + ":" + str(hashvalue) + ":" + str(Lowestpriorityj) + ":" + str(LowestSHA)  # delimiter
        proposedMsgHash = hashlib.sha512(str(gossip).encode('utf-8')).hexdigest()
        if proposedMsgHash not in NODEMESSAGES[id]:
            NODEMESSAGES[id].append(proposedMsgHash)
            sendmsg(id, gossip, env)


    yield env.timeout(0)
    # payload = NetworkMsg("hello world", id, env.now, "block", 1, 1)
    # sign = Ecdsa.sign(str(payload).encode('utf-8'), privateKey)
    #
    # sendmsg(id,payload,env)
    # yield env.timeout(0)
    # if id==1:
    # 	print_msglist()
    # exit(0)
    current_time = env.now
    yield env.timeout(0)
    LowestSHARecvd = []
    while env.now - current_time <= 33000:
        if not msgQueue[id].empty():
            time,msg = msgQueue[id].get()
            while time <= env.now :
                if chk_dup(msg, id) == True:
                    print("Time:", env.now, "msg recieved by", id, " for ", time, msg.message)
                    LowestSHARecvd.append(msg.message)
                    sendmsg(id, msg, env)
                else:
                    # print("Duplicate found")
                    pass
                #validate
                if not msgQueue[id].empty():
                    time,msg = msgQueue[id].get()
                else:
                    break
            # print("Time:", env.now, "msg recieved by", id, " for delay", delay)
            yield env.timeout(time - env.now)
            if chk_dup(msg, id) == True:
                print("Time:", env.now, "msg recieved by", id, " for ", time, msg.message)
                LowestSHARecvd.append(msg.message)
                sendmsg(id, msg, env)
            else:
                # print("Duplicate found")
                pass
            # print("Time:", env.now, "msg recieved by", id, " for ", time)
        else:
            # print("Q empty")
            yield env.timeout(1)
    # print("LOWEST SHA RECVD BY", id, "are")
    # print(LowestSHARecvd)
    minimumrcvdhash = min(LowestSHARecvd)
    yield env.timeout(0)
    if LowestSHA <= minimumrcvdhash:
        print("You are a block proposer", id)
        randomstring = PRG(random.randint(1,100000000))
        newblock = "newblockmsg : "+hashof(genesis)+str(randomstring)
        newblockmsg  = NetworkMsg(newblock,id,env.now, "blockproposal", round, 1)
        sendmsg(id,newblockmsg, env)

    yield env.timeout(0)
    current_time = env.now
    blockproposal = None
    while env.now - current_time <= 33000:
        if not msgQueue[id].empty():
            time,msg = msgQueue[id].get()
            while time <= env.now :
                if chk_dup(msg, id) == True:
                    print("Time:", env.now, "msg recieved by", id, " for ", time, msg.message)
                    LowestSHARecvd.append(msg.message)
                    sendmsg(id, msg, env)
                else:
                    # print("Duplicate found")
                    pass
                #validate
                if not msgQueue[id].empty():
                    time,msg = msgQueue[id].get()
                else:
                    break
            # print("Time:", env.now, "msg recieved by", id, " for delay", delay)
            if time -env.now < 0:
                break
            yield env.timeout(time - env.now)
            if chk_dup(msg, id) == True:
                print("Time:", env.now, "msg recieved by", id, " for ", time, msg.message)
                LowestSHARecvd.append(msg.message)
                sendmsg(id, msg, env)
            else:
                # print("Duplicate found")
                pass
            # print("Time:", env.now, "msg recieved by", id, " for ", time)
        else:
            # print("Q empty")
            yield env.timeout(1)





    # print("Exiting gossip loop")
    # print(id, ":", gsp_list[id])


if __name__=="__main__":
    main()
