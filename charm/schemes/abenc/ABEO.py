'''

'''
from charm.schemes.pksig.pksig_ecdsa import ECDSA
from charm.toolbox.pairinggroup import PairingGroup,ZR,G1,G2,GT,pair
from charm.toolbox.secretutil import SecretUtil
from charm.toolbox.ABEnc import ABEnc, Input, Output

from charm.toolbox.ecgroup import ECGroup,G
from charm.toolbox.eccurve import prime256v1
from charm.schemes.pksig.pksig_ecdsa import ECDSA

import time
import random
import hashlib 

class ABEO(ABEnc):

    def __init__(self, groupObj):
        ABEnc.__init__(self)
        global util, group
        util = SecretUtil(groupObj, debug)        
        self.group = groupObj
        

     
    def setup(self):
        g = self.group.random(G1)
        # g.setBystr("0",10)
        print("python")
        # print("new g is " + pk['g'])
        w = self.group.random(G2)
        v = self.group.random(G2)
        u = self.group.random(G2)
        h = self.group.random(G2)
        gp = self.group.random(G2)
        alpha = self.group.random(ZR)
        msk = gp ** alpha
        e_gg_alpha = pair(g,msk)
        pk = {'g':g,'w':w,'v':v,'u':u,'h':h,'e_gg_alpha':e_gg_alpha}
        # print(pk)
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
            attr[a_i] = self.group.hash(a_i)
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
    
    def veriKeygen(self, tk, pk, attr,attr_str):
        t1 = self.group.random(ZR)
        r_pr = self.group.random(ZR)  
        vk1 = (tk['tk1'] * (pk['w'] ** r_pr)) ** t1
        vk2 = (tk['tk2'] * (pk['g'] ** r_pr)) ** t1
        vk_i_3 = {}
        vk_i_4 = {}
        r_i_pr = {}
        for a_i in attr_str:
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
        
    def encrypt(self, policy_str, pk): 
        msg = self.group.random(GT)
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
                a_i = self.group.hash(p_i)
                C_i_3[j] = 1/((pk['u'] ** a_i * pk['h']) ** u_i)
                C_i_4[j] = pk['g'] ** u_i

        CT = {'C0':C0,'C1':C1,'C_i_2':C_i_2,'C_i_3':C_i_3,'C_i_4':C_i_4,'policy_str':policy_str}
        
        return (CT,msg)        
    
    
    def tranform(self, tk, CT,attr_str):
        policy = util.createPolicy(CT['policy_str'])
        pruned = util.prune(policy,attr_str)
        # 不满足策略
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
        # temp2 = 1
        # for i in pruned:
        #     j = i.getAttributeAndIndex()
        #     k = i.getAttribute()
        #     w_i[j] = coeffs[j]
        #     temp2 *= (pair(C_i_2[j] **w_i[j],vk['vk2']) * pair(C_i_3[j] **w_i[j],vk['vk_i_3'][k]) * pair(vk['vk_i_4'][k], C_i_4[j]** w_i[j]))
        
        # C_1_pr = pair(CT['C1'],vk['vk1'])/temp2
        CT_pr = {'C0':CT['C0'],'C_0_pr':C_0_pr}

        return CT_pr

    def verify(self, CT_pr, wk):
        
        return (CT_pr['C_0_pr'] ** wk) == CT_pr['C_1_pr']

    def decrypt(self,CT_pr, dk):
        return CT_pr['C0']/(CT_pr['C_0_pr'] ** (1/dk))
    
    def userDecrypt(self,CT,sk,attr_str):
        policy = util.createPolicy(CT['policy_str'])
        pruned = util.prune(policy,attr_str)
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
            temp1 *= (pair(C_i_2[j] **w_i[j],sk['sk2']) * pair(C_i_3[j] **w_i[j],sk['sk_i_3'][k]) * pair(C_i_4[j]** w_i[j], sk['sk_i_4'][k]))

        e_gg_alpha_u = pair(CT['C1'],sk['sk1']) / temp1
        m_pr = CT['C0'] /e_gg_alpha_u 
        return m_pr


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

def getattrs(MAX):
    attr_str = []
    for i in range(MAX):
        attr_str.append(str(i+1))
    return attr_str

def generateHashChain(n,hashstr):
    result = []
    result.append(hashlib.sha256(hashstr.encode()).digest())
    for i in range(n+1):
        temphash = result[i]
        result.append(hashlib.sha256(temphash).digest())
        temphash = result[i+1]
    return result   

def main():   

    groupObj = PairingGroup('SS512')
    
    abeo = ABEO(groupObj)
    
    attr_str = getattrs(30)
    # print(attr_str)
    policy_str = getpolicy(30,30)
    # print(policy_str)
    
    (pk, msk) = abeo.setup()
    t = abeo.group.fromstr("[6172776968119684165170291368128433652817636448173749093457023424948260385279837018774774149930982188956916913145008943931711059687988096415181819433817738, 8687587692191287108886119971783525001480020593934954052605681527814232399216375005546606067382536684351686344089456732201641997200939472924879001214689004]",10,G1)
    print(t)
    return
    group = ECGroup(prime256v1)
    ecdsa = ECDSA(group)
    (public_key, secret_key) = ecdsa.keygen(0)
    print(str(public_key['y']))
    signature = ecdsa.sign(public_key,secret_key,m)
    
    sk = abeo.privKeygen(pk, msk, attr_str) 
    (tk, dk) = abeo.tranKeygen(sk)
    (vk, wk,r_i,r_i_pr) = abeo.veriKeygen(tk, pk,sk['attr'],attr_str)
    (CT,msg) = abeo.encrypt(policy_str,pk)
    CT_pr = abeo.tranform(tk,CT,attr_str)
    if CT_pr is False:
        print("policy is not sasitified")
        return 
    m_pr = abeo.decrypt(CT_pr,dk)
    print("m_pr:",m_pr)
    if m_pr != msg:
        print("incorrect")
    
    return 

def generateSig(m):
    group = ECGroup(prime256v1)
    ecdsa = ECDSA(group)
    (public_key, secret_key) = ecdsa.keygen(0)
    print(str(public_key['y']))
    signature = ecdsa.sign(public_key,secret_key,m)
    return signature
if __name__ == "__main__":
    debug = False
    main()
   
