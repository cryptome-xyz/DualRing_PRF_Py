import sys
import time
import os
from utilities import *


def DualRing_PRF_setup(param_choice):
    """
    :param param_choice: an integer representing the choice of the parameters.
    1: Legendre fast
    2: Legendre medium
    3: Legendre slow
    4: power residue fast
    5: power residue medium
    6: power residue slow
    :return a dictionary of the public parameters pp
    """
    # get program start time
    st = time.time()
    if param_choice == 1:
        B = 12
        N = 32
        tau = 58
        t = 2
        L = 32768
    elif param_choice == 2:
        B = 11
        N = 128
        tau = 52
        t = 2
        L = 32768
    elif param_choice == 3:
        B = 11
        N = 512
        tau = 47
        t = 2
        L = 32768
    elif param_choice == 4:
        B = 4
        N = 32
        tau = 49
        t = 254
        L = 4096
    elif param_choice == 5:
        B = 6
        N = 128
        tau = 38
        t = 254
        L = 4096
    elif param_choice == 6:
        B = 6
        N = 512
        tau = 34
        t = 254
        L = 4096
    elif param_choice == 7:
        B = 4
        N = 8
        tau = 3
        t = 254
        L = 1024
    else:
        print("Invalid Choice")
        sys.exit()
    sec_param = 128
    p = 2 ** 127 - 1
    Fp = GF(p)
    g = Fp.primitive_element()
    M = 1024
    if param_choice == 7:
        M = 16
    listI = []
    for i in range(L):
        listI.append(Fp.random_element())
    pp = {
        "sec_param": sec_param,
        "p": p,
        "L": L,
        "t": t,
        "listI": listI,
        "M": M,
        "B": B,
        "N": N,
        "tau": tau,
        "g": g
    }

    print("Setup running time: {} seconds".format(time.time() - st))
    print('-' * 50)
    return pp


def DualRing_PRF_KeyGen(pp):
    """
    Generate a pair of secret and public keys
    :param pp: system parameters from setup
    :return: a pair of secret and public keys
    """
    st = time.time()
    p = pp["p"]
    Fp = GF(p)
    # secret key
    sk = Fp.random_element()
    pk = []

    for item in pp.get("listI"):
        pk.append(compute_PRF(sk + item, pp.get("t"), pp.get("g"), pp.get("p")))
    print("Keygen running time: {} seconds".format(time.time() - st))
    print('-' * 50)
    return [sk, pk]


def DualRing_PRF_sign(pp, PK, msg, sk, ind):
    """
    Compute DualRing-PRF signature
    :param pp: system parameters from setup
    :param PK: a list of ell public keys
    :param msg: a message to be signed
    :param sk: the secret key of the signer
    :param ind: signer's index (starting from 0)
    :return: DualRing-PRF signature
    """
    # may add check of the secret key (whether it corresponds to a public key in the PK list)
    sign_time = time.time()
    #######################################################
    # Preparation before signing                          #
    #######################################################
    total_bits = 0
    # obtain parameters from pp
    # sec_param = pp.get("sec_param")
    p = pp.get("p")
    L = pp.get("L")
    t = pp.get("t")
    listI = pp.get("listI")
    M = pp.get("M")
    B = pp.get("B")
    N = pp.get("N")
    tau = pp.get("tau")
    g = pp.get("g")
    Fp = GF(p)
    if not power_of_2(M) or not power_of_2(N):
        print("Invalid public parameters")
        sys.exit()
    ell = len(PK)

    #######################################################
    # Phase 1. Commit to mask, witness, randomness and    #
    # triples                                             #
    #######################################################
    st = time.time()
    # pick a random salt
    # conver the integer to 256 bits binary string
    salt = os.urandom(32)
    # pick random challenges for non-signers
    user_ch = []
    challenges = []  # ell lists of challenges, where each list has tau lists, where each list has B indices in [0,L-1]
    for l in range(ell):
        if l == ind:
            user_ch.append(b'')
            challenges.append([])
        else:
            user_random_seed = os.urandom(16)
            user_ch.append(user_random_seed)
            output = expand_to_index_elements(user_random_seed, tau * B, L)
            challenges.append([output[i: i + B] for i in range(0, len(output), B)])
    com_mpc_sd_list = []
    com_mask_sd_list = []
    T = []
    delta_k_list = []
    delta_c_list = []

    mask_share_tree_lists = []
    sum_r_shares = []
    list_share_mpc = []
    mpc_tree = []
    mask_tree = []
    sum_r_shares = []  # tau lists with each list has B elements
    for e in range(tau):
        # sample mask root seed
        sd_mask_e = os.urandom(16)
        mask_share_tree_e = []
        # expand sd_mask_e
        sd_mask_e_tree = tree_based_PRG(sd_mask_e, log(M, 2), 16)  # leafs are at log(M,2) index
        mask_tree.append(sd_mask_e_tree)
        mask_share_tree_list = []  # a list of M trees, where each tree has N leaves
        for k in range(M):
            mask_share_tree_list.append(tree_based_PRG(sd_mask_e_tree[log(M, 2)][k], log(N, 2), 16))
            # print(mask_share_tree_list[k][log(N, 2)])
        mask_share_tree_lists.append(mask_share_tree_list)
        # sample MPC root seed
        sd_mpc_e = os.urandom(16)
        # expand sd_mpc with leaves N
        sd_mpc_mpc_e_tree = tree_based_PRG(sd_mpc_e, log(N, 2), 16)  # a tree with N leaves
        mpc_tree.append(sd_mpc_mpc_e_tree)
        # expand seed to MPC shares
        share_mpc_e = []  # a list of N shares
        sum_key_share = 0
        sum_a_share = 0
        sum_b_share = 0
        sum_c_share = 0
        temp_com_mpc_sd_list = []
        temp_com_mask_list1 = []
        sum_r_shares_e = [0] * B
        for i in range(N):
            sd_mpc = sd_mpc_mpc_e_tree[log(N, 2)][i]
            # each share [0]: key share; [1],...,[B]: randomness share; [B + 1] share of a; [B + 2] share of b; [B + 3] share of c
            share_mpc = expand_to_Fp_elements(sd_mpc, B + 4, p, 16)
            share_mpc_e.append(share_mpc)
            sum_key_share += share_mpc[0]
            sum_a_share += share_mpc[B + 1]
            sum_b_share += share_mpc[B + 2]
            sum_c_share += share_mpc[B + 3]
            for b in range(B):
                sum_r_shares_e[b] += share_mpc[b + 1]
            # commit to  MPC seeds
            temp_com_mpc_sd_list.append(hash_commit(salt, e, 0, i, sd_mpc))
            # commit to mask shares
            temp_com_mask_list2 = []
            for k in range(M):
                sd_mask = mask_share_tree_list[k][log(N, 2)][i]
                temp_com_mask_list2.append(hash_commit(salt, e, k, i, sd_mask))
            temp_com_mask_list1.append(temp_com_mask_list2)
        com_mpc_sd_list.append(temp_com_mpc_sd_list)
        com_mask_sd_list.append(temp_com_mask_list1)
        sum_r_shares.append(sum_r_shares_e)
        # compute key adjustments
        delta_K_e = sk - sum_key_share
        delta_k_list.append(delta_K_e)
        # adjust the first key share
        share_mpc_e[0][0] = share_mpc_e[0][0] + delta_K_e
        # compute triple adjustments
        delta_c_e = sum_a_share * sum_b_share - sum_c_share
        delta_c_list.append(delta_c_e)
        # adjust the first triple share
        share_mpc_e[0][B + 3] = share_mpc_e[0][B + 3] + delta_c_e
        list_share_mpc.append(share_mpc_e)
        # compute residuosity symbols
        temp_T_list = []
        for b in range(B):
            pk_sum = 0
            for l in range(ell):
                if l == ind:
                    continue
                else:
                    pk_sum = (pk_sum + PK[l][challenges[l][e][b]]) % t
            T_e_b = (compute_PRF(sum_r_shares_e[b], t, g, p) - pk_sum) % t
            temp_T_list.append(T_e_b)
        T.append(temp_T_list)
    # define first round message
    sigma_1 = [com_mask_sd_list, com_mpc_sd_list, T, delta_k_list, delta_c_list]
    print("Phase 1 running time: {} seconds".format(time.time() - st))
    print('-' * 50)
    #######################################################
    # Phase 2. Commit to mask, witness, randomness and    #
    # triples                                             #
    #######################################################
    st = time.time()
    # concatenate all items to a string
    string = str(salt) + str(msg) + str(list_to_string(PK))
    for item in sigma_1:
        string += list_to_string(item)
    h_1 = get_challenge(string)
    # compute real signer's challenge
    # XOR non-signer's challenges
    signer_ch = h_1[:16]
    for l in range(ell):
        if l == ind:
            continue
        else:
            if len(signer_ch) != len(user_ch[l]):
                raise ValueError("Byte strings are not of equal length")
            else:
                temp = bytes(user_ch[l])
                signer_ch = bytes(xor_byte ^ temp for xor_byte, temp in zip(signer_ch, temp))
    user_ch[ind] = signer_ch
    # expand real signer's challenge
    output = expand_to_index_elements(user_ch[ind], B * tau, L)
    challenges[ind] = [output[i:i + B] for i in range(0, len(output), B)]
    acc = []
    delta_I_pi = []
    acc_tree = []
    perm_tree = []
    permuted_user_ind = []
    permuted_com_delta = []
    for e in range(tau):
        delta_I_pi_e = []
        acc_e = []
        acc_tree_e = []
        sd_perm_e = os.urandom(16)
        perm_e_tree = tree_based_PRG(sd_perm_e, log(M, 2), 16)
        perm_tree.append(perm_e_tree)
        permuted_user_ind_e = []
        permuted_com_delta_e = []
        for k in range(M):
            delta_I_e_k_pi = []
            mask_e_k = Fp(0)
            for i in range(N):
                int_value = Integer(int.from_bytes(mask_share_tree_lists[e][k][log(N, 2)][i], byteorder='big'))
                fp_element = Fp(int_value)
                mask_e_k += fp_element
            user_ind = []
            com_delta_e_k = []
            delta_I_e_k = []
            for j in range(ell):
                delta_I_e_k_j = []  # a list of B Fp elements
                for b in range(B):
                    delta_I_e_k_j.append(listI[challenges[j][e][b]] - mask_e_k)
                delta_I_e_k.append(delta_I_e_k_j)
                # elta_I_e_k_pi = [item for item in delta_I_e_k_j[ind]]
                # commit to offsets
                string = list_to_string(delta_I_e_k_j)
                com_delta_e_k.append(hash_commit(salt, e, k, 0, string))
                user_ind.append(j)
            delta_I_e_k_pi = [item for item in delta_I_e_k[ind]] # make a copy of delta_I_e_k_pi
            # randomly sample a permutation seed
            # permute the list
            permuted_user_ind_e_k = seeded_permutation(user_ind.copy(), perm_e_tree[log(M, 2)][k])
            permuted_user_ind_e.append(permuted_user_ind_e_k)
            permuted_com_delta_e_k = seeded_permutation(com_delta_e_k.copy(), perm_e_tree[log(M, 2)][k])
            # print(perm_e_tree[log(M, 2)][k])
            permuted_com_delta_e.append(permuted_com_delta_e_k)
            # accumulate the permuted commitments using Merkle tree
            # permuted_com_delta_e_k = []
            # for j in range(ell):
            # permuted_com_delta_e_k.append(com_delta_e_k[e][k][permuted_user_ind[j]])
            acc_e_k_tree, root_e_k = compute_merkle_root(permuted_com_delta_e_k, salt)
            # print(e, k, root_e_k)
            # print(e, k, permuted_com_delta_e_k)
            acc_tree_e.append(acc_e_k_tree)
            acc_e.append(root_e_k)
            delta_I_pi_e.append(delta_I_e_k_pi)
        # combine M accumulators with hash function
        delta_I_pi.append(delta_I_pi_e)
        permuted_user_ind.append(permuted_user_ind_e)
        # print(acc_e)
        string = list_to_string(acc_e)
        acc.append(hash_commit(salt, e, 0, 0, string))
        acc_tree.append(acc_tree_e)
        permuted_com_delta.append(permuted_com_delta_e)
    sigma_2 = acc

    print("Phase 2 running time: {} seconds".format(time.time() - st))
    print('-' * 50)

    #######################################################
    # Phase 3. Compute opened executions for              #
    # cut-and-choose                                      #
    #######################################################
    st = time.time()
    string = str(h_1)
    for item in sigma_2:
        string += list_to_string(item)
    h_2 = get_challenge(string)

    # expand h_2 to M indices from [0, M - 1]
    unopened_M = expand_to_index_elements(h_2, tau, M)
    print("Phase 3 running time: {} seconds".format(time.time() - st))
    print('-' * 50)
    #######################################################
    # Phase 4. Compute output values                      #
    #######################################################
    st = time.time()
    o = []
    for e in range(tau):
        o_e = []
        for b in range(B):
            o_e_b = (sk + listI[challenges[ind][e][b]]) * sum_r_shares[e][b]
            o_e.append(o_e_b)
        o.append(o_e)
    sigma_3 = o
    print("Phase 4 running time: {} seconds".format(time.time() - st))
    print('-' * 50)

    #######################################################
    # Phase 5. Compute challenges for sacrificing based   #
    # verification                                        #
    #######################################################
    st = time.time()
    string = str(h_2)
    for item in sigma_3:
        string += list_to_string(item)
    h_3 = get_challenge(string)
    # expand h_3 to get challenges for sacrificing protocol
    sacrificing_challenge_list = expand_to_Fp_elements(h_3, tau * (B + 1), p, 16)
    challenge_lambda = []
    for e in range(tau):
        challenge_lambda.append(sacrificing_challenge_list[e * B: (e + 1) * B])
    challenge_epsilon = sacrificing_challenge_list[tau * B:]
    print("Phase 5 running time: {} seconds".format(time.time() - st))
    print('-' * 50)

    #######################################################
    # Phase 6. Commit to views of sacrificing protocol    #
    #######################################################
    st = time.time()
    list_alpha_e = []
    list_beta_e = []
    list_alpha_e_i = []
    list_beta_e_i = []
    list_gamma_e_i = []
    delta_z = []
    # each share [0]: key share; [1],...,[B]: randomness share; [B + 1] share of a; [B + 2] share of b; [B + 3] share of c
    for e in range(tau):
        alpha_e = 0
        beta_e = 0
        temp_list_alpha_e_i = []
        temp_list_beta_e_i = []
        temp_list_gamma_e_i = []
        z_e = []
        sum_lambda_o_e = Fp(0)
        for b in range(B):
            sum_lambda_o_e += challenge_lambda[e][b] * o[e][b]
        real_z_e = Fp(0)
        fault_z_e = Fp(0)
        for i in range(N):
            alpha_e_i = list_share_mpc[e][i][B + 1] + challenge_epsilon[e] * list_share_mpc[e][i][0]
            temp_list_alpha_e_i.append(alpha_e_i)
            alpha_e += alpha_e_i
            sum_e_i_lambda_r = Fp(0)
            share_I_e_i = []
            sum_lambda_r_I_e = Fp(0)
            real_sum_lambda_r_I_e = Fp(0)
            for b in range(B):
                lambda_r_e_i_b = list_share_mpc[e][i][b + 1] * challenge_lambda[e][b]
                sum_e_i_lambda_r += lambda_r_e_i_b
                if i == 0:
                    share_I_e_i_b = Fp(Integer(int.from_bytes(mask_share_tree_lists[e][unopened_M[e]][log(N, 2)][i], byteorder='big'))) + delta_I_pi[e][unopened_M[e]][b]
                else:
                    share_I_e_i_b = Fp(
                        Integer(int.from_bytes(mask_share_tree_lists[e][unopened_M[e]][log(N, 2)][i], byteorder='big')))
                share_I_e_i.append(share_I_e_i_b)
                sum_lambda_r_I_e -= challenge_lambda[e][b] * list_share_mpc[e][i][b + 1] * share_I_e_i_b
                real_sum_lambda_r_I_e -= challenge_lambda[e][b] * list_share_mpc[e][i][b + 1] * listI[challenges[ind][e][b]]
            z_e_i = sum_lambda_r_I_e
            real_z_e_i = real_sum_lambda_r_I_e
            beta_e_i = list_share_mpc[e][i][B + 2] + sum_e_i_lambda_r
            temp_list_beta_e_i.append(beta_e_i)
            beta_e += beta_e_i
            if i == 0:
                z_e_i = z_e_i + sum_lambda_o_e
                real_z_e_i = real_z_e_i + sum_lambda_o_e
            real_z_e += real_z_e_i
            fault_z_e += z_e_i
            z_e.append(z_e_i)
        delta_z_e = real_z_e - fault_z_e
        z_e[0] = z_e[0] + delta_z_e
        delta_z.append(delta_z_e)
        gamma_e = 0
        for i in range(N):
            # compute gamma
            gamma_e_i = alpha_e * list_share_mpc[e][i][B + 2] + beta_e * list_share_mpc[e][i][B + 1] - list_share_mpc[e][i][B + 3] + challenge_epsilon[e] * z_e[i]
            gamma_e += gamma_e_i
            temp_list_gamma_e_i.append(gamma_e_i)
        list_alpha_e.append(alpha_e)
        list_beta_e.append(beta_e)
        list_alpha_e_i.append(temp_list_alpha_e_i)
        list_beta_e_i.append(temp_list_beta_e_i)
        list_gamma_e_i.append(temp_list_gamma_e_i)

    sigma_4 = [list_alpha_e, list_beta_e, delta_z, list_alpha_e_i, list_beta_e_i, list_gamma_e_i]
    print("Phase 6 running time: {} seconds".format(time.time() - st))
    print('-' * 50)

    #######################################################
    # Phase 7. Challenge on sacrificing protocol          #
    #######################################################
    st = time.time()
    string = str(h_3)
    for item in sigma_4:
        string += list_to_string(item)
    h_4 = get_challenge(string)
    unopened_N = expand_to_index_elements(h_4, tau, N)
    print("Phase 7 running time: {} seconds".format(time.time() - st))
    print('-' * 50)

    #######################################################
    # Phase 8. Open executions for cut-and-choose and MPC #
    # views                                               #
    #######################################################
    st = time.time()
    path_seed_mpc = []
    path_seed_mask = []
    path_mask_share = []
    path_perm = []
    MT_proof = []
    delta_I = []
    MT_index = []
    com_sd_mpc = []
    com_sd_mask = []
    h_1_second_half = h_1[16:]
    # calculate the signature sizes
    for e in range(tau):
        path_seed_mpc_e = tree_based_PRG_open(unopened_N[e], mpc_tree[e])
        path_seed_mpc.append(path_seed_mpc_e)
        path_seed_mask_e = tree_based_PRG_open(unopened_M[e], mask_tree[e])
        path_seed_mask.append(path_seed_mask_e)
        path_mask_share_e = tree_based_PRG_open(unopened_N[e], mask_share_tree_lists[e][unopened_M[e]])
        path_mask_share.append(path_mask_share_e)
        path_perm_e = tree_based_PRG_open(unopened_M[e], perm_tree[e])
        path_perm.append(path_perm_e)
        ind_e = permuted_user_ind[e][unopened_M[e]].index(ind)
        MT_index.append(ind_e)
        # print(ind_e)
        # MT_leaf.append(permuted_com_delta[e][unopened_M[e]][ind_e])
        MT_proof_e = compute_auth_path(acc_tree[e][unopened_M[e]], ind_e)
        MT_proof.append(MT_proof_e)
        # print(MT_proof[e])
        delta_I.append(delta_I_pi[e][unopened_M[e]])
        com_sd_mpc.append(com_mpc_sd_list[e][unopened_N[e]])
        com_sd_mask.append(com_mask_sd_list[e][unopened_N[e]][unopened_M[e]])
    print("Phase 8 running time: {} seconds".format(time.time() - st))
    print('-' * 50)

    sig = {
        "salt": salt,
        "h_1_second_half": h_1_second_half,
        "h_2": h_2,
        "h_4": h_4,
        "path_perm": path_perm,
        "path_seed_mask": path_seed_mask,
        "path_mask_share": path_mask_share,
        "MT_index": MT_index,
        "MT_proof": MT_proof,
        "path_seed_mpc": path_seed_mpc,
        "delta_k_list": delta_k_list,
        "delta_c_list": delta_c_list,
        "o": o,
        "delta_I": delta_I,
        "list_alpha_e": list_alpha_e,
        "list_beta_e": list_beta_e,
        "delta_z": delta_z,
        "com_sd_mpc": com_sd_mpc,
        "com_sd_mask": com_sd_mask,
        "user_ch": user_ch
    }
    print("Signing running time: {} seconds".format(time.time() - sign_time))
    print('-' * 50)

    total_bits = 0


    for items in sig.values():
        if isinstance(items, bytes):
            bits = len(items) * 8
            total_bits += bits
        else:
            for item in items:
                if isinstance(item, bytes):
                    bits = len(item) * 8
                    total_bits += bits
                elif isinstance(item, list):
                    bits = get_bit_length_of_list(item)
                    total_bits += bits
                elif isinstance(item, int):
                    bits = item.bit_length()
                    total_bits += bits
                elif isinstance(item, dict):
                    bits = get_bit_length_of_dict(item)
                    total_bits += bits
                else:
                    total_bits += Integer(item).bit_length()
    print("Signature size is (bits)", total_bits)
    print('-'*50)





    return sig


def DualRing_PRF_verify(pp, PK, msg, sig):
    st = time.time()
    p = pp.get("p")
    L = pp.get("L")
    t = pp.get("t")
    listI = pp.get("listI")
    M = pp.get("M")
    B = pp.get("B")
    N = pp.get("N")
    tau = pp.get("tau")
    g = pp.get("g")
    Fp = GF(p)
    if not power_of_2(M) or not power_of_2(N):
        print("Invalid public parameters")
        sys.exit()
    ell = len(PK)

    salt = sig.get("salt")
    h_1_second_half = sig.get("h_1_second_half")
    h_2 = sig.get("h_2")
    h_4 = sig.get("h_4")
    path_perm = sig.get("path_perm")
    path_seed_mask = sig.get("path_seed_mask")
    path_mask_share = sig.get("path_mask_share")
    MT_index = sig.get("MT_index")
    MT_proof = sig.get("MT_proof")
    path_seed_mpc = sig.get("path_seed_mpc")
    delta_k_list = sig.get("delta_k_list")
    delta_c_list = sig.get("delta_c_list")
    o = sig.get("o")
    delta_z = sig.get("delta_z")
    delta_I = sig.get("delta_I")
    list_alpha_e = sig.get("list_alpha_e")
    list_beta_e = sig.get("list_beta_e")
    com_sd_mpc = sig.get("com_sd_mpc")
    com_sd_mask = sig.get("com_sd_mask")
    user_ch = sig.get("user_ch")

    challenges = []
    for j in range(ell):
        output = expand_to_index_elements(user_ch[j], tau * B, L)
        challenges.append([output[i: i + B] for i in range(0, len(output), B)])

    # expand h_2 to M indices from [0, M - 1]
    unopened_M = expand_to_index_elements(h_2, tau, M)
    # recompute h_3
    string = str(h_2)
    for item in o:
        string += list_to_string(item)
    h_3 = get_challenge(string)
    sacrificing_challenge_list = expand_to_Fp_elements(h_3, tau * (B + 1), p, 16)
    challenge_lambda = []
    for e in range(tau):
        challenge_lambda.append(sacrificing_challenge_list[e * B: (e + 1) * B])
    challenge_epsilon = sacrificing_challenge_list[tau * B:]
    unopened_N = expand_to_index_elements(h_4, tau, N)
    acc = []
    com_mask_share = []
    com_mpc_sd = []
    T = []
    list_alpha_e_i = []
    list_beta_e_i = []
    list_gamma_e_i = []
    for e in range(tau):
        temp_alpha_e_i = []
        temp_beta_e_i = []
        temp_gamma_e_i = []
        # get N - 1 MPC party seeds from path_seed_mpc
        mpc_seed_e = tree_based_PRG_recompute(unopened_N[e], path_seed_mpc[e], 16)
        mpc_seed_e.insert(unopened_N[e], b'')
        # get N - 1 mask shares
        mask_share_e = tree_based_PRG_recompute(unopened_N[e], path_mask_share[e], 16)
        mask_share_e.insert(unopened_N[e], b'')
        sum_lambda_o = Fp(0)
        for b in range(B):
            sum_lambda_o += challenge_lambda[e][b] * o[e][b]
        alpha_e_bar = Fp(0)
        beta_e_bar = Fp(0)
        share_mpc_e = []
        z_e = []
        com_mpc_sd_e = []
        com_mask_share_e_k_bar = []
        # print(mpc_seed_e)
        for i in range(N):
            if i == unopened_N[e]:
                share_mpc_e.append([])
                z_e.append(Fp(0))
                com_mpc_sd_e.append(com_sd_mpc[e])
                com_mask_share_e_k_bar.append(com_sd_mask[e])
                temp_alpha_e_i.append([])
                temp_beta_e_i.append([])
            else:
                # each share [0]: key share; [1],...,[B]: randomness share; [B + 1] share of a; [B + 2] share of b; [B + 3] share of c
                share_mpc = expand_to_Fp_elements(mpc_seed_e[i], B + 4, p, 16)

                # recompute the mpc seed commitment and mask commitment
                com_mpc_sd_e_i = hash_commit(salt, e, 0, i, mpc_seed_e[i])
                com_mpc_sd_e.append(com_mpc_sd_e_i)
                com_mask_share_e_k_bar_i = hash_commit(salt, e, unopened_M[e], i, mask_share_e[i])
                com_mask_share_e_k_bar.append(com_mask_share_e_k_bar_i)
                if i == 0:
                    share_mpc[0] = share_mpc[0] + delta_k_list[e]
                    share_mpc[B + 3] = share_mpc[B + 3] + delta_c_list[e]
                share_mpc_e.append(share_mpc)
                sum_lambda_r_e = Fp(0)
                sum_lambda_r_I_e = Fp(0)
                for b in range(B):
                    if i == 0:
                        # Integer(int.from_bytes(mask_share_tree_lists[e][unopened_M[e]][log(N, 2)][i], byteorder='big')))
                        share_I_e_i_b = Fp(Integer(int.from_bytes(mask_share_e[i], byteorder='big'))) + delta_I[e][b]
                    else:
                        share_I_e_i_b = Fp(Integer(int.from_bytes(mask_share_e[i], byteorder='big')))
                    sum_lambda_r_e += challenge_lambda[e][b] * share_mpc[b + 1]
                    sum_lambda_r_I_e -= challenge_lambda[e][b] * share_mpc[b + 1] * share_I_e_i_b
                # recompute sacrificing shares
                alpha_e_i = share_mpc[B + 1] + challenge_epsilon[e] * share_mpc[0]
                temp_alpha_e_i.append(alpha_e_i)
                beta_e_i = share_mpc[B + 2] + sum_lambda_r_e
                temp_beta_e_i.append(beta_e_i)
                alpha_e_bar += alpha_e_i
                beta_e_bar += beta_e_i
                z_e_i = sum_lambda_r_I_e
                if i == 0:
                    z_e_i = z_e_i + sum_lambda_o
                    z_e_i = z_e_i + delta_z[e]
                z_e.append(z_e_i)
        sum_gamma_bar = Fp(0)
        for i in range(N):
            if i == unopened_N[e]:
                gamma_e_i = 0
            else:
                gamma_e_i = list_alpha_e[e] * share_mpc_e[i][B + 2] + list_beta_e[e] * share_mpc_e[i][B + 1] - share_mpc_e[i][B + 3] + challenge_epsilon[e] * z_e[i]
                sum_gamma_bar += gamma_e_i
            temp_gamma_e_i.append(gamma_e_i)
        # compute missing share
        temp_alpha_e_i[unopened_N[e]] = list_alpha_e[e] - alpha_e_bar
        temp_beta_e_i[unopened_N[e]] = list_beta_e[e] - beta_e_bar
        temp_gamma_e_i[unopened_N[e]] = list_alpha_e[e] * list_beta_e[e] - sum_gamma_bar
        T_e = []
        list_alpha_e_i.append(temp_alpha_e_i)
        list_beta_e_i.append(temp_beta_e_i)
        list_gamma_e_i.append(temp_gamma_e_i)
        for b in range(B):
            pk_e_b = 0
            for j in range(ell):
                pk_e_b = (pk_e_b + PK[j][challenges[j][e][b]]) % t
            T_e_b = (compute_PRF(o[e][b], t, g, p) - pk_e_b) % t
            T_e.append(T_e_b)
        T.append(T_e)
        # recompute permutation seeds
        perm_rand = tree_based_PRG_recompute(unopened_M[e], path_perm[e], 16)
        # print(unopened_M[e])
        mask_seed = tree_based_PRG_recompute(unopened_M[e], path_seed_mask[e], 16)
        perm_rand.insert(unopened_M[e], b'')
        mask_seed.insert(unopened_M[e], b'')
        permuted_com_delta_e = []
        acc_e = []
        com_mask_share_e = []
        for k in range(M):
            com_mask_share_e_k = []
            if k == unopened_M[e]:
                com_mask_share_e.append(com_mask_share_e_k_bar)
            else:
                # compute all mask shares from mask seed
                # mask_share_tree_list.append(tree_based_PRG(sd_mask_e_tree[log(M, 2)][k], log(N, 2), 16))
                mask_shares_e_k = tree_based_PRG(mask_seed[k], log(N, 2), 16)
                mask_e_k = Fp(0)
                for i in range(N):
                    com_mask_share_e_k.append(hash_commit(salt, e, k, i, mask_shares_e_k[log(N, 2)][i]))
                    mask_e_k += Fp(Integer(int.from_bytes(mask_shares_e_k[log(N, 2)][i], byteorder='big')))
                com_mask_share_e.append(com_mask_share_e_k)
                user_ind = []
                com_delta_e_k = []
                for j in range(ell):
                    delta_I_e_k_j = []
                    user_ind.append(j)
                    for b in range(B):
                        delta_I_e_k_j.append(listI[challenges[j][e][b]] - mask_e_k)
                    string = list_to_string(delta_I_e_k_j)
                    com_delta_e_k.append(hash_commit(salt, e, k, 0, string))

                permuted_com_delta_e_k = seeded_permutation(com_delta_e_k.copy(), perm_rand[k]) # throw index out of range
                # print(perm_rand[k])

                permuted_com_delta_e.append(permuted_com_delta_e_k)
                # print(e,k,permuted_com_delta_e_k)
                acc_e_k_tree, root_e_k = compute_merkle_root(permuted_com_delta_e_k, salt)
                acc_e.append(root_e_k)
                # print(e, k, root_e_k)
        # print(len(com_mask_share_e))
        string = list_to_string(delta_I[e])
        com_delta_I_e_k_bar = hash_commit(salt, e, unopened_M[e], 0, string)
        acc_e_k_bar = recompute_MT_root(com_delta_I_e_k_bar, salt, MT_proof[e], MT_index[e], ell)
        # print(acc_e_k_bar)
        acc_e.insert(unopened_M[e], acc_e_k_bar)
        string = list_to_string(acc_e)
        acc.append(hash_commit(salt, e, 0, 0, string))
        com_mask_share.append(com_mask_share_e)
        com_mpc_sd.append(com_mpc_sd_e)

    h_1_prime = reduce(lambda x, y: bytes(a ^ b for a, b in zip(x, y)), user_ch)
    h_1_prime = h_1_prime + h_1_second_half

    com_mask_share_new = []
    for e in range(tau):
        com_mask_share_e_new = []
        for i in range(N):
            com_mask_share_e_i_new = []
            for k in range(M):
                com_mask_share_e_i_new.append(com_mask_share[e][k][i])
            com_mask_share_e_new.append(com_mask_share_e_i_new)
        com_mask_share_new.append(com_mask_share_e_new)

    sigma_1_prime = [com_mask_share_new, com_mpc_sd, T, delta_k_list, delta_c_list]
    string = str(salt) + str(msg) + str(list_to_string(PK))
    for item in sigma_1_prime:
        string += list_to_string(item)
    h_1 = get_challenge(string)

    string = str(h_1)
    for item in acc:
        string += list_to_string(item)
    h_2_prime = get_challenge(string)

    sigma_4_prime = [list_alpha_e, list_beta_e, delta_z, list_alpha_e_i, list_beta_e_i, list_gamma_e_i]
    string = str(h_3)
    for item in sigma_4_prime:
        string += list_to_string(item)
    h_4_prime = get_challenge(string)
    if h_1 != h_1_prime or h_2 != h_2_prime or h_4 != h_4_prime:
        print("Reject: Invalid signature")
        sys.exit()
    else:
        print("Accept: Valid Signature")
    print("Verification running time: {} seconds".format(time.time() - st))
    print('-' * 50)

def main():
    # 1: Legendre fast
    # 2: Legendre medium
    # 3: Legendre slow
    # 4: power residue fast
    # 5: power residue medium
    # 6: power residue slow
    # 7: test set with small but insecure parameters

    pp = DualRing_PRF_setup(4)
    # key1 = DualRing_PRF_KeyGen(pp)
    key2 = DualRing_PRF_KeyGen(pp)
    # key3 = DualRing_PRF_KeyGen(pp)
    # key4 = DualRing_PRF_KeyGen(pp)

    ell = 8
    PK = []
    for i in range(ell):
        PK.append(key2[1])

    msg = "Hello World"
    sig = DualRing_PRF_sign(pp, PK, msg, key2[0], 1)
    DualRing_PRF_verify(pp, PK, msg, sig)


if __name__ == "__main__":
    main()
