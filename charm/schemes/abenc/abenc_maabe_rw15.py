"""
Rouselakis - Waters Efficient Statically-Secure Large-Universe Multi-Authority Attribute-Based Encryption

| From:             Efficient Statically-Secure Large-Universe Multi-Authority Attribute-Based Encryption
| Published in:     Financial Crypto 2015
| Available from:   http://eprint.iacr.org/2015/016.pdf
| Notes:

* type:          attribute-based encryption (public key)
* setting:       bilinear pairing group of prime order
* assumption:    complex q-type assumption

:Authors:		Yannis Rouselakis
:Date:      	11/12
"""

from charm.toolbox.pairinggroup import *
from charm.cryptobase import *
from charm.toolbox.secretutil import SecretUtil
from charm.toolbox.ABEncMultiAuth import ABEncMultiAuth

debug = False


class MaabeRW15(ABEncMultiAuth):
    def random_message(self):
        return group.random(GT)

    def exp(self, value):
        return group.init(ZR, value)

    def get_authority(self, x):
        i = x.find("@")
        if (i == -1):
            print("Error: No @ char in [attribute@authority] name")
            return

        j = x.find("_")
        if (j == -1):
            return x[i + 1:]
        else:
            return x[i + 1:j]

    def extract_attribute_name(self, attribute):
        i = attribute.rfind("_")
        if (i == -1):
            return attribute
        else:
            return attribute[:i]

    def __init__(self, groupObj, verbose=False):
        global util, group
        group = groupObj
        util = SecretUtil(group, verbose)

    def setup(self):
        g1 = group.random(G1)
        g2 = group.random(G2)
        egg = pair(g1, g2)
        H = lambda x: group.hash(x, G2)
        F = lambda x: group.hash(x, G2)
        gp = {'g1': g1, 'g2': g2, 'egg': egg, 'H': H, 'F': F}
        return gp

    def authsetup(self, gp, name):
        alpha, y = group.random(), group.random()
        egga = gp['egg'] ** alpha
        gy = gp['g1'] ** y
        pk = {'name': name, 'egga': egga, 'gy': gy}
        sk = {'name': name, 'alpha': alpha, 'y': y}
        return pk, sk

    def single_keygen(self, gp, gid, sk, attr):
        # the authority's name is included in the secret key
        # check here if gid name is legal
        # checking if attribute is legal
        if (sk['name'] != self.get_authority(attr)):
            print("Error: Attribute ", attr, " does not belong to authority ", sk['name'])
            return

        t = group.random()
        K = gp['g2'] ** sk['alpha'] * gp['H'](gid) ** sk['y'] * gp['F'](attr) ** t
        # K = gp['g2']**sk['alpha'] * gp['F'](attr)**t
        KP = gp['g1'] ** t

        return {'user': gid, 'auth': sk['name'], 'attr': attr, 'K': K, 'KP': KP}

    def keygen(self, gp, gid, authSkChain, attributes):
        # check here if gid name is legal

        sks = {}
        for attr in attributes:
            auth = self.get_authority(attr)
            sk = self.single_keygen(gp, gid, authSkChain[auth], attr)
            sks[attr] = sk

        return {'GID': gid, 'Attributes': attributes, 'Chain': sks}

    def encrypt(self, gp, pks, message, policy_str):
        s = group.random()  # secret to be shared
        w = group.init(ZR, 0)  # 0 to be shared

        policy = util.createPolicy(policy_str)
        a_list = util.getAttributeList(policy)
        # print("\n\n THE A-LIST IS", a_list,"\n\n")
        # for i in a_list:
        #	print(self.getAuth(i))

        secretShares = util.calculateSharesDict(s, policy)  # These are correctly set to be exponents in Z_p
        zeroShares = util.calculateSharesDict(w, policy)

        C0 = message * (gp['egg'] ** s)

        C1, C2, C3, C4 = {}, {}, {}, {}
        for i in a_list:
            auth = self.get_authority(i)
            attr = self.extract_attribute_name(i)  # take out the possible underscore
            tx = group.random()
            C1[i] = gp['egg'] ** secretShares[i] * pks[auth]['egga'] ** tx
            C2[i] = gp['g1'] ** (-tx)
            C3[i] = pks[auth]['gy'] ** tx * gp['g1'] ** zeroShares[i]
            C4[i] = gp['F'](attr) ** tx

        return {'Policy': policy_str, 'C0': C0, 'C1': C1, 'C2': C2, 'C3': C3, 'C4': C4}

    def decrypt(self, gp, sk_chain, ct):
        hgid = gp['H'](sk_chain['GID'])

        policy = util.createPolicy(ct['Policy'])
        z = util.getCoefficients(policy)
        #		print("\n\n THE COEFF-LIST IS", z,"\n\n")

        pruned_list = util.prune(policy, sk_chain['Attributes'])
        #		print("\n\n THE PRUNED-LIST IS", pruned_list,"\n\n")

        if (pruned_list == False):
            return group.init(GT, 1)

        B = group.init(GT, 1)
        for i in range(len(pruned_list)):
            x = pruned_list[i].getAttribute()  # without the underscore
            y = pruned_list[i].getAttributeAndIndex()  # with the underscore
            # print(x,y)
            # print(z[y])
            B *= (ct['C1'][y] * pair(ct['C2'][y], sk_chain['Chain'][x]['K']) * pair(ct['C3'][y], hgid) * pair(
                sk_chain['Chain'][x]['KP'], ct['C4'][y])) ** z[y]

        return ct['C0'] / B


def pretty_print(init_str, my_dict, tab=""):
    types_enum = ["ZP", "G1", "G2", "GT"]
    if len(init_str) > 0:
        print(init_str)
    for (k, v) in my_dict.items():
        if isinstance(v, dict):
            print(tab, k, ": ", type(v))
            pretty_print("", v, tab + "    ")
        elif isinstance(v, str):
            print(tab, k, ": ", v)
        elif isinstance(v, set):
            print(tab, k, ": ", v)
        elif isinstance(v, pairing):
            print(tab, k, ": ", types_enum[v.type])
        else:
            print(tab, k, ": ", type(v))
    if tab == "":
        print("\n")


def main():
    pass
    # curve = 'MNT224'
    #
    # groupObj = PairingGroup(curve)
    # scheme = MAABE_RW12(groupObj)
    # print("Curve = ", curve)
    #
    # ID = InitBenchmark()
    # startAll(ID)
    # gp = scheme.GlobalSetup()
    # EndBenchmark(ID)
    # boxGS = getResAndClear(ID, "GSetup(" + curve + ")", "Done!")
    #
    # # prettyPrint("The global parameters are ", gp)
    #
    # pks, sks = {}, {}
    #
    # ID = InitBenchmark()
    # startAll(ID)
    # (pk, sk) = scheme.AuthSetup(gp, "UT")
    # EndBenchmark(ID)
    # boxAS = getResAndClear(ID, "ASetup(" + "UT" + ")", "Done!")
    #
    # pks[pk['name']] = pk
    # sks[sk['name']] = sk
    #
    # (pk, sk) = scheme.AuthSetup(gp, "OU")
    # pks[pk['name']] = pk
    # sks[sk['name']] = sk
    #
    # # prettyPrint("The authority public key chain is ", pks)
    # # prettyPrint("The authority secret key chain is ", sks)
    #
    # ID = InitBenchmark()
    # startAll(ID)
    # key = scheme.keygen(gp, "YANNIS", sks, {"STUDENT@UT", "PHD@UT"})
    # EndBenchmark(ID)
    # boxKG = getResAndClear(ID, "KeyGen", "Done!")
    #
    # # prettyPrint("The secret key is ", key)
    #
    # m = scheme.random_message()
    # policy = '(STUDENT@UT or PROFESSOR@OU) and (STUDENT@UT or MASTERS@OU)'
    #
    # ID = InitBenchmark()
    # startAll(ID)
    # ct = scheme.encrypt(gp, pks, m, policy)
    # EndBenchmark(ID)
    # boxEC = getResAndClear(ID, "Encrypt", "Done!")
    #
    # # prettyPrint("The ciphertext is ", ct)
    #
    # ID = InitBenchmark()
    # startAll(ID)
    # res = scheme.decrypt(gp, key, ct)
    # EndBenchmark(ID)
    #
    # if res == m:
    #     fin = "Successful Decryption :)"
    # else:
    #     fin = "Failed Decryption :("
    #
    # boxDE = getResAndClear(ID, "Decrypt", fin)
    #
    # # print(fin)
    #
    # print(formatNice(boxGS, boxAS, boxKG, boxEC, boxDE))


if __name__ == '__main__':
    debug = True
    main()
