#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import sys
import pandas as pd
import json
from state_infomation_generation import *

class CodeqlResult:
    def __init__(self, state_id):
        self.state_id = state_id
        self.value_start_line = 0
        self.value_end_line = 0
        self.value_start_column = 0
        self.value_end_column = 0

        self.file_name = ''
        self.state_value = ''

        self.instument_fucntion = '_it_state_record'

    def get_instument_string(self):
        return " " + self.instument_fucntion + "(" + str(self.state_id) + ',' + '(uint64_t)' + self.state_value + ");"

    def get_declare_string(self):
        ds = '''
#ifndef AFL_PROTOCOL_INSTRUMENT
#define AFL_PROTOCOL_INSTRUMENT
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif
void _it_state_record(int64_t id, uint64_t value);
//__attribute__((weak)) void _it_state_record(int64_t id, uint64_t value){abort()};
#ifdef __cplusplus
}
#endif /* __cplusplus */
#endif /* SFUZZ_INSTRUMENT */

'''
        return ds

    def get_declare_check_string(self):
        return '#ifndef AFL_PROTOCOL_INSTRUMENT'


class StateInrustment:

    def __init__(self, info_gen: StateInfomationGeneration) -> None:
        self.records = []
        self.info_gen = info_gen

    def read_codeql_result(self, file):
        df = pd.read_csv(file, header=None)
        for index, row in df.iterrows():
            for temp in row[3].split('\n'):
                if temp == '':
                    continue
                try:
                    content = json.loads(temp)
                except Exception as e:
                    print(temp)
                    raise e
                
                self.new_record(content)
        
        self.deal_codeql_result()
                
    def new_record(self, content):
        state_id = self.info_gen.get_state_id_by_name(content['StateName'])
        if state_id == 0:
            return
        
        codeql_result = CodeqlResult(state_id)
        codeql_result.file_name = content['FileName']
        codeql_result.value_start_line = content['StartLine']
        codeql_result.value_start_column = content['StartColumn']
        codeql_result.value_end_line = content['EndLine']
        codeql_result.value_end_column = content['EndColumn']

        self.records.append(codeql_result)

    def print_codeql_result(self):
        for record in self.records:
            print(record.state_id, record.file_name, record.value_start_line, record.value_start_column,
                record.value_end_line, record.value_end_column, record.state_value)
            print(record.get_instument_string())
            print('----------')

    def write_content_to_file(self, file_path, content, start_line, start_column, prefix_start_line, prefix_start_column):
        with open(file_path, 'rb') as f:
            lines = f.readlines()
            #add { symbol
            lines[prefix_start_line - 1] = lines[prefix_start_line - 1][:prefix_start_column] + \
                b"{" + lines[prefix_start_line - 1][prefix_start_column:]
            #add instrument function
            lines[start_line - 1] = lines[start_line - 1][:start_column+1] + \
                bytes(content, encoding='utf-8') + b"}" + lines[start_line - 1][start_column+1:]
        with open(file_path, 'wb') as f:
            f.writelines(lines)

    def write_declare_to_file(self, file_path, content, check_string):
        with open(file_path, 'rb') as f:
            lines = f.readlines()
            start_line = lines[0]
            if check_string in str(start_line, encoding='utf-8'):
                return
            lines.insert(0, bytes(content, encoding='utf-8'))
        with open(file_path, 'wb') as f:
            f.writelines(lines)

    def get_content_from_file(self, file_path, start_line, start_column, end_line, end_column):
        with open(file_path, 'rb') as f:
            lines = f.readlines()
            content = b''

            if start_line == end_line:
                content = lines[start_line - 1][start_column - 1: end_column - 1]
                return str(content, encoding='utf-8')

            for i in range(start_line, end_line + 1):
                if i == start_line:
                    content += lines[i - 1][start_column - 1:]
                elif i == end_line:
                    content += lines[i - 1][:end_column - 1]
                else:
                    content += lines[i - 1]
            return str(content, encoding='utf-8')
        
    def deal_codeql_result(self):
        for record in self.records:
            expr = self.get_content_from_file(record.file_name, record.value_start_line,
                                        record.value_start_column, record.value_end_line, record.value_end_column)
            record.state_value = expr.split('=')[0].strip()

            if record.state_value[-1] == '-' or record.state_value[-1] == '+' or record.state_value[-1] == '*' or record.state_value[-1] == '/' or record.state_value[-1] == '%' or record.state_value[-1] == '&' or record.state_value[-1] == '^' or record.state_value[-1] == '|':
                record.state_value = record.state_value[:-1]

            elif (record.state_value[-1] == '<' and record.state_value[-2] == '<') or (record.state_value[-1] == '>' and record.state_value[-2] == '>') :
                record.state_value = record.state_value[:-2]

            #print(record.state_value)

    
    def instrument_codeql_result(self):
        for record in self.records:
            content = record.get_instument_string()
            self.write_content_to_file(record.file_name, content, record.value_end_line, record.value_end_column+1, record.value_start_line, record.value_start_column-1)

    
    def instrument_declare(self):
        file_record = []
        for record in self.records:
            if record.file_name not in file_record:
                file_record.append(record.file_name)
                declare_content = record.get_declare_string()
                declare_check_string = record.get_declare_check_string()
                self.write_declare_to_file(record.file_name, declare_content, declare_check_string)
                
    def do_intrument(self):
        self.instrument_codeql_result()
        self.instrument_declare()

    def collect_and_do_intrument(self, codeql_result_file: str):
        self.read_codeql_result(codeql_result_file)
        self.do_intrument()



if __name__ == "__main__":    
    state_collection = StateCollection()
    state_collection.obtain_state_machines_pd(sys.argv[1])
    state_collection.obtain_state_relation_pd(sys.argv[2])
    state_collection.obtain_state_and_transitions()
    state_collection.judge_all_state_machine_type()

    state_metric_collector = StateMetricCollection(state_collection)
    state_metric_collector.collect_state_col(sys.argv[3])
    state_metric_collector.collect_state_global_access(sys.argv[4])
    state_metric_collector.collect_state_global_assign(sys.argv[5])

    state_infomation_generation = StateInfomationGeneration(state_collection)
    state_infomation_generation.generate_info_list()

    state_inrustment = StateInrustment(state_infomation_generation)
    state_inrustment.read_codeql_result(sys.argv[6])
    state_inrustment.print_codeql_result()

    state_infomation_generation.generate_json(sys.argv[7])
