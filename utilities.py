from sage.all import *
from hashlib import shake_128
from hashlib import sha3_256
import random


def power_of_2(n):
    """
    Check if n is a power of 2
    :param n:
    :return: True or False
    """
    return n > 0 and (n & (n - 1)) == 0


'''def shake_128_func(input_value, output_bytes):
    shake = shake_128()
    if isinstance(input_value, bytes):
        shake.update(input_value)
    elif isinstance(input_value, int):
        shake.update(repr(input_value).encode('utf-8'))
    else:
        shake.update(input_value.encode('utf-8'))
    return shake.digest(output_bytes)'''

def shake_128_byte(input_value, output_bytes):
    shake = shake_128()
    # shake_128().update(input_value)
    shake.update(input_value)
    return shake.digest(output_bytes)

'''def sha3_256_func(input_value):
    sha256 = sha3_256()
    if isinstance(input_value, bytes):
        sha256.update(input_value)
    elif isinstance(input_value, int):
        sha256.update(repr(input_value).encode('utf-8'))
    else:
        sha256.update(input_value.encode('utf-8'))
    return sha256.digest()'''



def sha3_256_string(str):
    sha256 = sha3_256()
    sha256.update(str.encode('utf-8'))
    return sha256.digest()

def compute_PRF(value, t, g, p):
    if t == 2:
        return floor(1 / 2 * (1 - kronecker(value, p)))
    elif t == 254:
        Fp = GF(p)
        if value % p == 0:
            return 0
        else:
            for i in range(t):
                temp = value / g ** i
                if temp ** ((p - 1) // t) == Fp(1):
                    return i
    else:
        print("Invalid value of t")
        sys.exit()


def tree_based_PRG(seed, depth, output_bytes):
    """
    Expand the seed to 2^depth values with tree structure
    :param seed: the root seed
    :param depth: the depth of the tree
    :param output_bytes: the output_length of the tree
    :return: the dictionary of the tree with index being the level and value being the 2^level values
    """
    '''if isinstance(seed, bytes):
        tree = {0: seed}  # level 0 root seed as bytes
    elif isinstance(seed, int):
        tree = {0: repr(seed).encode('utf-8')}
    else:
        tree = {0: seed.encode('utf-8')}'''
    tree = {0: [seed]}
    for level in range(depth):
        values = []
        for i in range(2 ** level):
            parent = tree[level][i]
            children = shake_128_byte(parent, 2 * output_bytes)
            left_child, right_child = children[:16], children[16:]
            values.extend([left_child, right_child])
        tree[level + 1] = values
    return tree


def tree_based_PRG_open(index, tree):
    """
    Find authentication path for a specific index
    :param index: index of unopened leaf node
    :param tree: PRG tree
    :return: authentication path
    """
    path = {}
    depth = len(tree.keys()) - 1
    for i in range(depth):
        ind = floor(index / 2 ** i)
        if ind % 2 == 0:
            path.update({i: tree[depth - i][ind + 1]})
        else:
            path.update({i: tree[depth - i][ind - 1]})
    return path


def tree_based_PRG_recompute(index, path, output_bytes):
    """
    Recompute all values except for value[index] of the PRG tree
    :param index: the unrevealed index
    :param path: open path of PRG tree
    :param output_bytes: output bytes for shake-128
    :return:
    """
    # re-expand the path
    output = []
    for expand_time in path.keys():
        ind = floor(index / 2 ** expand_time)
        if expand_time == 0:
            output.append([path[expand_time]])
        else:
            values = [path[expand_time]]
            for i in range(2 ** expand_time - 1):
                parent = values[i]
                children = shake_128_byte(parent, 2 * output_bytes)
                left_child, right_child = children[:16], children[16:]
                values.extend([left_child, right_child])
            if ind % 2 == 0:
                output.append(values[2 ** expand_time - 1:])
            else:
                output.insert(0, values[2 ** expand_time - 1:])
    result = []
    for items in output:
        for item in items:
            result.append(item)
    return result


def expand_to_Fp_elements(sd, num_elements, p, output_bytes):
    """
    Expand a seed to any number of field p elements
    :param sd: seed
    :param num_elements: number of field p elements desired
    :param p: prime p
    :param output_bytes: output bytes for shake_128
    :return: a list of num_elements field p elements
    """
    # print(sd)
    output = shake_128_byte(sd, num_elements * output_bytes)
    Fp = GF(p)
    result = [None] * num_elements
    for i in range(num_elements):
        element = output[i * 16: (i + 1) * 16]
        integer_value = int.from_bytes(element, byteorder='big')
        result[i] = Fp(integer_value)

    return result


def get_challenge(input):
    return sha3_256_string(input)


def expand_to_index_elements(sd, num, length):
    """
    Expand a seed to indices of listI
    :param sd: seed
    :param num: number of indices desired
    :param length: total length of listI
    :return: a list of indices in [0,L-1]
    """
    bit_length = log(length, 2)
    byte_length = ceil(bit_length * num / 8)
    output = shake_128_byte(sd, byte_length)
    bit_out = bin(int.from_bytes(output, byteorder='big'))[2: num * bit_length]
    result = [None] * num
    # convert every bit_length bits to an integer
    for i in range(num):
        element = bit_out[i * bit_length: (i + 1) * bit_length]
        result[i] = int(element, 2)

    return result


def hash_commit(salt, e, k, i, sd):
    string = f'{salt}|{e}|{k}|{i}{sd}' #str(salt) + str(e) + str(k) + str(i) + str(sd)
    return sha3_256_string(string)


def list_to_string(input):
    '''if not isinstance(input, list):
        return str(input)'''
    return ''.join(str(item) for item in flatten(input))


def seeded_permutation(input, sd=None):
    if sd is not None:
        sd = str(sd) if not isinstance(sd, (int, float, str, bytes, bytearray)) else sd
        random.seed(sd)
    random.shuffle(input)
    return input


def compute_merkle_root(data, randomness):
    # expand randomness to a rand_list with the same length as data
    rand = shake_128_byte(randomness, len(data) * 16)
    rand_list = [rand[i * 16: (i + 1) * 16] for i in range(len(data))]
    # for i in range(len(data)):
        # rand_list.append(rand[i * 16: (i + 1) * 16])
    if len(data) % 2 == 1:
        data.append(data[-1])
        rand_list.append(rand_list[-1])

    tree = {0: [sha3_256_string(str(data[i]) + str(rand_list[i])) for i in range(len(data))]}
    level = 0
    while len(tree[level]) > 1:
        tree[level + 1] = []
        for i in range(0, len(tree[level]), 2):
            node = sha3_256_string(str(tree[level][i]) + str(tree[level][i + 1]))
            tree[level + 1].append(node)
        level += 1
        if len(tree[level]) % 2 == 1 and len(tree[level]) > 1:
            tree[level].append(tree[level][-1])
    return tree, tree[level][0]


def compute_auth_path(tree, index):
    path = []
    for level in range(len(tree) - 1):
        sibling_index = index - 1 if index % 2 else index + 1
        path.append(tree[level][sibling_index])
        index = index // 2
    return path


def recompute_MT_root(leaf, randomness, auth_path, index, length):
    # expand randomness to a rand_list with the same length as data
    rand = shake_128_byte(randomness, length * 16)
    rand_list = []
    for i in range(length):
        rand_list.append(rand[i * 16: (i + 1) * 16])
    rand = rand_list[index]

    current_hash = sha3_256_string(str(leaf) + str(rand))
    for sibling_hash in auth_path:
        if index % 2 == 0:
            current_hash = sha3_256_string(str(current_hash) + str(sibling_hash))
        else:
            current_hash = sha3_256_string(str(sibling_hash) + str(current_hash))
        index = index // 2

    return current_hash

def remove_duplicates_dict(input_dict):
    # Create an empty dictionary to store unique values
    unique_values_dict = {}
    # Iterate over the original dictionary
    for key, value in input_dict.items():
        # Convert the list of values into a set to remove duplicates
        unique_values = set(value)
        # Assign the unique values to the key in the new dictionary
        unique_values_dict[key] = list(unique_values)

    return unique_values_dict


def get_byte_length_of_dict(input_dict):
    total_bytes = 0
    unique_dict = remove_duplicates_dict(input_dict)
    for key, value in unique_dict.items():
        key_bytes = key.bit_length()/8
        value_bytes = len(value)
        total_bytes += key_bytes + value_bytes
    return total_bytes

def remove_duplicates_list(input_list):
    seen = set()
    output_list = []
    for item in input_list:
        if item not in seen:
            output_list.append(item)
            seen.add(item)
    return output_list
def get_byte_length_of_list(input_list):
     #for item in input_list:
        # print("item", item)
         #print("type",type(item))
         #print(sys.getsizeof(item))
    byte = 0
    unique_list = remove_duplicates_list(flatten(input_list))
    for item in unique_list:
        if isinstance(item, bytes):
            byte += len(item)
        else:
            byte += Integer(item).bit_length()/8
    return byte

def get_bit_length_of_dict(input_dict):
    total_bits = 0
    unique_dict = remove_duplicates_dict(input_dict)
    for key, value in unique_dict.items():
        key_bits = key.bit_length()
        value_bits = len(value) * 8
        total_bits += key_bits + value_bits
    return total_bits


def get_bit_length_of_list(input_list):
    # for item in input_list:
    # print("item", item)
    # print("type",type(item))
    # print(sys.getsizeof(item))
    bits = 0
    unique_list = remove_duplicates_list(flatten(input_list))
    for item in unique_list:
        if isinstance(item, bytes):
            bits += len(item) * 8
        else:
            bits += Integer(item).bit_length()
    return bits

