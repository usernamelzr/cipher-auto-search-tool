from error_handler import raise_error
from util import int_to_bits, bits_to_int
from encryption import encrypt
from hash import hash
import numpy as np

def parse_testvector_file_block_cipher(file_path):
    f = open(file_path, "r")
    plaintext_int = None
    ciphertext_int = None
    round_key_list = []
    # 0: plaintext, 1: main key, 2: ciphertext
    environment_flag = -1
    line = f.readline()
    while line:
        line = line.split()
        if not line:
            line = f.readline()
            continue
        if line[0].startswith("//") or line[0].startswith("#"):
            line = f.readline()
            continue
        if line[0] == ".PLAINTEXT":
            environment_flag = 0
        elif line[0] == ".KEY":
            subkey_num = int(line[1])
            environment_flag = 1
        elif line[0] == ".CIPHERTEXT":
            environment_flag = 2
        elif environment_flag != -1:
            value = int(line[0], base=0)
            if environment_flag == 0:
                plaintext_int = value
                environment_flag = -1
            elif environment_flag == 1:
                round_key_list.append(value)
                if len(round_key_list) == subkey_num:
                    environment_flag = -1
            elif environment_flag == 2:
                ciphertext_int = value
                environment_flag = -1
        line = f.readline()
    f.close()
    if plaintext_int is None:
        raise_error("文件{}中找不到明文值!".format(file_path))
    return plaintext_int, round_key_list, ciphertext_int

def parse_testvector_file_hash(file_path):
    f = open(file_path, "r")
    message_list = []
    iv_int = None
    digest_int = None
    # 0: iv, 1: message, 2: digest
    environment_flag = -1
    line = f.readline()
    while line:
        line = line.split()
        if not line:
            line = f.readline()
            continue
        if line[0].startswith("//") or line[0].startswith("#"):
            line = f.readline()
            continue
        if line[0] == ".IV":
            environment_flag = 0
        elif line[0] == ".MESSAGE":
            environment_flag = 1
            message_num = int(line[1])
        elif line[0] == ".DIGEST":
            environment_flag = 2
        elif environment_flag != -1:
            value = int(line[0], base=0)
            if environment_flag == 0:
                iv_int = value
                environment_flag = -1
            elif environment_flag == 1:
                message_list.append(value)
                if len(message_list) == message_num:
                    environment_flag = -1
            elif environment_flag == 2:
                digest_int = value
                environment_flag = -1
        line = f.readline()
    f.close()
    if iv_int is None:
        raise_error("文件{}中找不到IV值!".format(file_path))
    return iv_int, message_list, digest_int

def verify_block_cipher(plaintext_int, main_key_list, ciphertext_int, cipher, cipher_round_number, cipher_block_size, subkey_expand_tuple):
    plaintext_bits = int_to_bits(plaintext_int, cipher_block_size, False)
    _, tested_ciphertext_bits, _ = encrypt(cipher, cipher_round_number, cipher_block_size, subkey_expand_tuple, 1, given_plaintext_bits=plaintext_bits, given_main_key_list=main_key_list)
    assert len(tested_ciphertext_bits) == cipher_block_size
    if isinstance(tested_ciphertext_bits[0], np.ndarray):
        tested_ciphertext_bits = [int(tested_ciphertext_bits[i][0]) for i in range(cipher_block_size)]
    tested_ciphertext_int = bits_to_int(tested_ciphertext_bits, False)
    print("\n加密后密文值为: {}".format(hex(tested_ciphertext_int)))
    if ciphertext_int is not None:
        if ciphertext_int == tested_ciphertext_int:
            print("\n算法实现正确性验证成功!")
        else:
            print("\n算法实现正确性验证失败!")

def verify_hash(iv_int, message_list, digest_int, cipher, cipher_round_number, cipher_block_size, message_expand_tuple):
    iv_bits = int_to_bits(iv_int, cipher_block_size, False)
    _, _, tested_digest_bits = hash(cipher, cipher_round_number, cipher_block_size, message_expand_tuple, 1, 1, iv_bits, [message_list])
    assert len(tested_digest_bits) == cipher_block_size
    if isinstance(tested_digest_bits[0], np.ndarray):
        tested_digest_bits = [int(tested_digest_bits[i][0]) for i in range(cipher_block_size)]
    tested_digest_int = bits_to_int(tested_digest_bits, False)
    print("\n哈希后的摘要值为: {}".format(hex(tested_digest_int)))
    if digest_int is not None:
        if tested_digest_int == digest_int:
            print("\n算法实现正确性验证成功!")
        else:
            print("\n算法实现正确性验证失败!")