import json
import web3
import time
import sys
import random
import copy

from web3.auto import w3

from web3.contract import ConciseContract
from solc import compile_files
from charm.toolbox.pairinggroup import PairingGroup,ZR,G1,G2,GT,pair
from charm.toolbox.secretutil import SecretUtil
from charm.toolbox.ABEnc import ABEnc, Input, Output
from charm.toolbox.ecgroup import ECGroup,G
from charm.toolbox.eccurve import secp384r1
from charm.schemes.pksig.pksig_ecdsa import ECDSA
import hashlib
debug = False
class ABEO(ABEnc):

    def __init__(self, groupObj):
        ABEnc.__init__(self)
        global util, group
        util = SecretUtil(groupObj, debug)        
        self.group = groupObj
        

     
    def setup(self):
        g = self.group.random(G1)
        w = self.group.random(G2)
        v = self.group.random(G2)
        u = self.group.random(G2)
        h = self.group.random(G2)
        gp = self.group.random(G2)
        alpha = self.group.random(ZR)
        msk = gp ** alpha
        e_gg_alpha = pair(g,msk)
        pk = {'g':g,'w':w,'v':v,'u':u,'h':h,'e_gg_alpha':e_gg_alpha}
        return (pk, msk)
    
    def privKeygen(self, pk, msk, attr_str):
        r = self.group.random(ZR)
        g = pk['g']
        w = pk['w']
        v = pk['v']
        h = pk['h']
        u = pk['u']
        sk1 = msk * (w ** r)
        sk2 = g ** r
        sk_i_3 = {}
        sk_i_4 = {}
        attr = {}
        for a_i in attr_str:
            r_i = self.group.random()
            attr[a_i] = self.group.random()
            sk_i_3[a_i] = g ** r_i
            sk_i_4[a_i] = (((u ** attr[a_i]) * h) ** r_i) / (v ** r) 
        sk = {'sk1':sk1,'sk2':sk2,'sk_i_3':sk_i_3,'sk_i_4':sk_i_4,'attr':attr}
        
        return sk


    def tranKeygen(self, sk):
        t0 = self.group.random(ZR)
        tk1 = sk['sk1'] ** t0
        tk2 = sk['sk2'] ** t0
        tk_i_3 = {}
        tk_i_4 = {}
        for i in sk['attr']:
            tk_i_3[i] = sk['sk_i_3'][i] ** t0
        for i in sk['attr']:
            tk_i_4[i] = sk['sk_i_4'][i] ** t0
        dk = t0 
        tk = {'tk1':tk1,'tk2':tk2,'tk_i_3':tk_i_3,'tk_i_4':tk_i_4}
        
        return(tk, dk)
    
    def veriKeygen(self, tk, pk, attr):
        t1 = self.group.random(ZR)
        r_pr = self.group.random(ZR)  
        vk1 = (tk['tk1'] * (pk['w'] ** r_pr)) ** t1
        vk2 = (tk['tk2'] * (pk['g'] ** r_pr)) ** t1
        vk_i_3 = {}
        vk_i_4 = {}
        r_i_pr = {}
        for a_i in attr:
            r_i_pr[a_i] = self.group.random(ZR)
            vk_i_3[a_i] = (tk['tk_i_3'][a_i] * (pk['g'] ** r_i_pr[a_i])) ** t1
            vk_i_4[a_i] = (tk['tk_i_4'][a_i] * (((pk['u'] ** attr[a_i]) * pk['h']) ** r_i_pr[a_i]) * (pk['v'] ** (-r_pr))) ** t1
        
        wk = t1
        vk = {'vk1':vk1,'vk2':vk2,'vk_i_3':vk_i_3,'vk_i_4':vk_i_4}

        return (vk, wk,r_pr,r_i_pr)
    def generateCipher(self, policy_str, attr, pk, n):
        ciphers = []
        msgs = []
        for i in range(n):
            msg = self.group.random(GT)
            ciphers.append({})
            ciphers[i] = self.encrypt(policy_str, attr, pk,msg)
            msgs.append(msg)
        return (ciphers,msgs)
    
    def generateTkVk(self,sk,pk,n):
        keys =[]
        Rs = []
        for i in range(n):
            keys.append({})
            Rs.append({})
            (keys[i]['tk'], Rs[i]['dk']) = self.tranKeygen(sk)
            (keys[i]['vk'],Rs[i]['wk'],Rs[i]['r_pr'],Rs[i]['r_i_pr']) = self.veriKeygen(keys[i]['tk'],pk,sk['attr']) 
        return (keys,Rs)

    def encrypt(self, policy_str, attr, pk, msg): 
        policy = util.createPolicy(policy_str)
        a_list = util.getAttributeList(policy)
        u = self.group.random(ZR)
        v_i = util.calculateSharesList(u, policy)
        C0 = (pk['e_gg_alpha'] ** u) * msg
        C1 = pk['g'] ** u
        C_i_2 = {}
        C_i_3 = {}
        C_i_4 = {}
        for i in range(len(a_list)):
            u_i = self.group.random()
            if v_i[i][0] == a_list[i]:
                j = a_list[i]
                C_i_2[j] = (pk['w'] ** v_i[i][1]) * (pk['v'] ** u_i)
                p_i = v_i[i][0].getAttribute()
                C_i_3[j] = 1/((pk['u'] ** attr[p_i] * pk['h']) ** u_i)
                C_i_4[j] = pk['g'] ** u_i

        CT = {'C0':C0,'C1':C1,'C_i_2':C_i_2,'C_i_3':C_i_3,'C_i_4':C_i_4,'attr':attr,'policy_str':policy_str}
        
        return (CT)        
    
    def transformByCloud(self,keys,ciphers):
        n = len(ciphers)
        transresult = []
        for i in range(n):
            transresult.append(self.transform(keys[i]['tk'],keys[i]['vk'],ciphers[i]))
        return transresult

    def transform(self, tk, vk, CT):
        policy = util.createPolicy(CT['policy_str'])
        pruned = util.prune(policy,CT['attr'])
        if pruned == False:
            return False
        coeffs = util.getCoefficients(policy)
        w_i = {}
        C_i_2 = CT['C_i_2']
        C_i_3 = CT['C_i_3']
        C_i_4 = CT['C_i_4']
        temp1 = 1
        
        for i in pruned:
            j = i.getAttributeAndIndex()
            k = i.getAttribute()
            w_i[j] = coeffs[j]
            temp1 *= (pair(C_i_2[j] **w_i[j],tk['tk2']) * pair(C_i_3[j] **w_i[j],tk['tk_i_3'][k]) * pair(C_i_4[j]** w_i[j], tk['tk_i_4'][k]))
                    
        C_0_pr = pair(CT['C1'],tk['tk1']) / temp1
        temp2 = 1
        for i in pruned:
            j = i.getAttributeAndIndex()
            k = i.getAttribute()
            w_i[j] = coeffs[j]
            temp2 *= (pair(C_i_2[j] **w_i[j],vk['vk2']) * pair(C_i_3[j] **w_i[j],vk['vk_i_3'][k]) * pair(vk['vk_i_4'][k], C_i_4[j]** w_i[j]))
        
        C_1_pr = pair(CT['C1'],vk['vk1'])/temp2
        CT_pr = {'C0':CT['C0'],'C_0_pr':C_0_pr,'C_1_pr':C_1_pr}
        
        return CT_pr

    def verify(self, CT_pr, wk):
        
        return (CT_pr['C_0_pr'] ** wk) == CT_pr['C_1_pr']

    def decrypt(self,CT_pr, dk):
        return CT_pr['C0']/(CT_pr['C_0_pr'] ** (1/dk))

def compile_source_file(file_path):
   with open(file_path, 'r') as f:
      source = f.read()

   return compile_source(source)

def deploy_contract(w3, contract_interface):
    tx_hash = w3.eth.contract(
        abi=contract_interface['abi'],
        bytecode=contract_interface['bin']).deploy()

    address = w3.eth.getTransactionReceipt(tx_hash)['contractAddress']
    return address

# 获得随机的policy
def getpolicy(len, MAX):
    if len == 1:
        return  str(random.randint(1,MAX))
    else:
        condition = [" or "," and "]
        r = random.randint(0,1)
        if len%2 == 0:
            return "(" + getpolicy(len/2,MAX) + condition[r] + getpolicy(len/2,MAX) + ")"
        else:
            return "(" + getpolicy((len-1)/2,MAX) + condition[r] + getpolicy((len+1)/2,MAX) + ")"

def getattr(MAX):
    attr_str = []
    for i in range(MAX):
        attr_str.append(str(i+1))
    return attr_str
# 生成哈希链
def generateHashChain(n,hashstr):
    result = []
    result.append(hashlib.sha256(str(hashstr).encode()).digest())
    for i in range(n-1):
        temphash = result[i]
        result.append(hashlib.sha256(temphash).digest())
        temphash = result[i+1]
    return result

# 生成数字签名病并公布公钥
# def generateSigkey():
#     sig_key = SigningKey.generate(curve = SECP256k1)
#     verify_key = sig_key.get_verifying_key()
#     fo = open("pub.txt","w")
#     fo.write(verify_key.to_string().hex())
#     return (sig_key,verify_key)
def ge():
    group = ECGroup(secp384r1)
    print(group)
    ecdsa = ECDSA(group)
    print(ecdsa)
    (public_key, secret_key) = ecdsa.keygen(0)
    print(public_key)
    msg = "hello world! this is a test message."
    signature = ecdsa.sign(public_key, secret_key, msg)
    print(signature)
    (ok,r) = ecdsa.verify(public_key, signature, msg)
    print(ok,r)
# 生成merkle根
def generateMerkleRoot(objs):
    data = []
    n = len(objs)
    for i in range(n):
        data.append(str(hashlib.sha256(str(objs[i]).encode()).hexdigest()))
    while(n> 1 ):
        k = 0
        i = 0
        while(i < n):
            if i < n-1:
                data[k] = str(hashlib.sha256(str(data[i] + data[i+1]).encode()).hexdigest())
                i += 2
                k += 1
            else:
                data[k] = data[i]
                break
        n = int((n + 1)/2)
    return data[0]
# 讲tk，vk写入文件，便于矿工计算merkle根
def sendTkVk(keys):
    fo = open("keys.txt","w")
    fo.write("")
    fo.close()
    fo = open("keys.txt","w+")
    for i in keys:
        fo.write(str(i) + "#")
    fo.close()

def main():
    ge()
    # 生成用户属性以及访问策略
    attr_str = getattr(3)
    policy_str = getpolicy(3,3)
    # 群参数初始化
    groupObj = PairingGroup('SS512')
    abeo = ABEO(groupObj)
    (pk,msk) = abeo.setup()
    sk = abeo.privKeygen(pk, msk, attr_str)
    # 生成一系列密文 
    n = 10
    (ciphers,msgs) = abeo.generateCipher(policy_str,sk['attr'],pk,n)
    ciphersroot = generateMerkleRoot(ciphers)
    # 生成tk，vk，以及生成时的一系列参数
    (keys,Rs) = abeo.generateTkVk(sk,pk,n)
    # 生成转化秘钥的merkle根
    keysroot = generateMerkleRoot(keys)
    # 生成密文的merkle根
    cipherroot = generateMerkleRoot(ciphers)

    # 将转化秘钥放到文件中-----发送给云
    sendTkVk(keys)
    #生成hashchain
    hashstr = "this is a hash"
    hashchain = generateHashChain(n+1,hasattr)
    # 生成数字签名的私钥和公钥
    # (sig_key,verify_key) = generateSigkey()
    # 编译智能合约
    compile_sol = compile_files(['/home/xinlei/BABEO/ABEO.sol'])
    contractid, contract_interface = compile_sol.popitem()
    # 与以太坊的链接状态
    # 解锁账户
    user = w3.eth.accounts[0]
    cloud = w3.eth.accounts[1]
    w3.personal.unlockAccount(user,'')
    w3.personal.unlockAccount(cloud,'')
    
    print("用户账户：",user)
    print("用户账户余额：",w3.eth.getBalance(user))
    print("云账户：",cloud)
    print("云账户余额：",w3.eth.getBalance(cloud))
    tx_hash = w3.eth.contract(abi=contract_interface['abi'],bytecode=contract_interface['bin']).constructor().transact({'from':user,'value':10})
    tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)

    contract_address = tx_receipt['contractAddress']

    # 获取合约实例
    contract_instance = w3.eth.contract(address=contract_address, abi=contract_interface['abi'])
    
    # 设置用于支付酬金的哈希值，以及密文的merkle根
    re = contract_instance.functions.sethash(hashchain[n],cipherroot,n).transact({'from':user,'gas':6000000})
    receipt = w3.eth.waitForTransactionReceipt(re)
    log = contract_instance.events.sethashevent().processReceipt(receipt)
    print(log)
    # 云收到转化秘钥
    # 云进行转化计算
    hashvalue = {}
    sig = ""
    last = n
    transform = {}
    for i in range(n):
        CT_pr = abeo.transform(keys[i]['tk'],keys[i]['vk'],ciphers[i])
        # signature = sig_key.sign(str(CT_pr).encode(),hashfunc=hashlib.sha512,sigencode=ecdsa.util.sigencode_string_canonize)
        print("sig is",signature)
        # if verify_key.verify(signature,str(CT_pr).encode(),hashfunc=hashlib.sha512,sigdecode=ecdsa.util.sigdecode_string) is False:
            # print("签名验证错误")
        m_pr = abeo.decrypt(CT_pr,Rs[i]['dk'])
        if m_pr == msgs[i]:
            last = i
            transform = CT_pr 
            sig = str(signature.hex())
            print("transform is",transform)
            print("sig is",sig)
            break
        # 发送哈希值给云
        hashvalue = hashchain[n-1-i]
    # 用户解密出现错误，申请矿工仲裁
    # 用户提供转化结果，以及一系列生成转化秘钥的参数
    if last is not n+1:
        re1 = contract_instance.functions.charge(str(transform)+"#",sig+"#",str(keys[last]['tk'])+"#",str(keys[last]['vk'])+"#",str(Rs[i])).transact({'from':user,'gas':22000000})
        receipt1 = w3.eth.waitForTransactionReceipt(re1)
        # log = contract_instance.events.chargeevent().processReceipt(receipt1)
        
    else:
        print("oook")
    
    # 验证哈希值支付酬金 
    print(hashvalue,cipherroot)
    re2 = contract_instance.functions.verifyHash(hashvalue,cipherroot).transact({'from':cloud,'gas':22000000})
    receipt2 = w3.eth.waitForTransactionReceipt(re2)
    log = contract_instance.events.verifyHashevent().processReceipt(receipt2)
    print(log)
    

    print("用户账户：",user)
    print("用户账户余额：",w3.eth.getBalance(user))
    print("云账户：",cloud)
    print("云账户余额：",w3.eth.getBalance(cloud))

if __name__ == "__main__":
    main()
