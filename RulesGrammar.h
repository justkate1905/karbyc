#ifndef RULESGRAMMAR_H
#define RULESGRAMMAR_H

#include <iostream>
#include <string>
#include <fstream>
#include <map>
#include <locale>
#include <boost/spirit/include/qi.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/bind.hpp>
#include <boost/spirit/include/phoenix.hpp>
#include <boost/spirit/include/qi_char_class.hpp>
#include <boost/locale/encoding_utf.hpp>
#include <boost/spirit/include/qi_lexeme.hpp>
#include <boost/spirit/include/qi_raw.hpp>

namespace Logic
{
	using boost::locale::conv::utf_to_utf;
	namespace qi = boost::spirit::qi;
	namespace ascii = boost::spirit::ascii;
	using boost::spirit::ascii::space;
	namespace unicode = boost::spirit::standard_wide;
	using namespace unicode;
	using namespace std;
	using namespace qi;
	using namespace boost::spirit;
	namespace phx = boost::phoenix;
	typedef int size_opcode;
	typedef std::string str_t;
	typedef str_t::iterator str_t_it;

	//структура хранения переменных в компиляторе
	//addr - адрес переменной в исполняемом файле
	//name - имя переменной в исходном коде
	struct variables{
		int addr = 0;
		int buff_addr;
		int type=0;
		int var_num = 1;
		str_t name;
		str_t name_buff;
		str_t temp_name;
		int temp_addr;
		int funcType = 0;
	};
	struct functions{
		str_t func_name;
		int funcId;
		int addr;
		int param=0;
		int ret_var=0;
		short int func_num = 0;
		vector<str_t> func_param;
	};
	
	struct func_service{
		str_t name;
		int addr;
		int param_num;
	};
	//структура представления операндов математических операций
	//first - первый операнд
	//second - второй операнд
	struct operand{
		int first;
		int second;
	};
	
	
	//структура представления простых арифметических операций
	struct signs{
		int PLUS = 0x1003;
		int MINUS = 0x1007;
		int MULTI = 0x100B;
		int DIV = 0x100F;
	};


	template <typename Iterator>
	class RulesGrammar : public qi::grammar <Iterator,  qi::space_type >
	{
		//переменные
		variables v;
		functions f;
		func_service serv;
		//мат.операции
		signs s;
		//операнды
		operand op_term, op_factor;
		//переменные для хранения значения переменных, типа данных и флага переменная-число
		int num=0, type = 0x00AB, var_flag=0, buff_flag=0, count_op = 0;
		
		std::string var_name = " ", math_exp, str_value, sign, name1;
		//вектор кодов операций
		vector <size_opcode> opcodes;
		vector<int> stack, var_stack; 
		//словарь всех переменных
		map<str_t, int> var_v;
		map<str_t, int> func_v;
		vector <func_service> function_list;
		vector<size_opcode> params;
		//вектор опкодов математического выражения в обратной польской записи		
		vector<int> math_reverse_form;
		//объявление правил
		qi::rule<Iterator, qi::space_type> start_programm, programm, name, variable,associate, binding,
											uint_bind, double_bind,expression, term,factor,cond,start_prog, 
											condition, operations, stream, init,id,strings, functionName,
											func_defenition, global_prog, param,return_val, call_function,
											assoc, give_param, int_p;

	public:
		RulesGrammar() : RulesGrammar::base_type(global_prog)
		{
				global_prog = *(func_defenition)>> start_programm;
				//начало программы
				start_programm = qi::lit("start")[boost::bind(&RulesGrammar::PushOpcode, this, 0x00A1)]
												[boost::bind(&RulesGrammar::SetType, this,0)]
								>>'('>>qi::char_(')')>>qi::char_('{')>>programm>>'}';
								
				func_defenition = qi::lit("deff")[boost::bind(&RulesGrammar::SetType, this,1)]>>
											functionName[boost::bind(&RulesGrammar::SetFuncProperty, this)] >> '('>> 
											(-(param % ',' ))[boost::bind(&RulesGrammar::PushParam, this)]	>>')'>>'{'>>
											programm[boost::bind(&RulesGrammar::PushFuncVars, this)] >>
											(-(return_val))>>qi::lit('}')[boost::bind(&RulesGrammar::PushOpcode, this, 0x01B0)]
														[boost::bind(&RulesGrammar::PushCodeSize,this)];
				return_val  = qi::lit("return")>>(name [boost::bind(&RulesGrammar::PushOpcode,this, 0x01B5)]
														[boost::bind(&RulesGrammar::SetBuffName,this)]
														[boost::bind(&RulesGrammar::PushBuffAddr,this)]
												|expression[boost::bind(&RulesGrammar::PushOpcode,this, 0x01B4)]
													[boost::bind(&RulesGrammar::PushOpcode,this, 0x00AA)]
												| int_[boost::bind(&RulesGrammar::PushOpcode,this, 0x01B3)]
														[phx::bind(&RulesGrammar::PushOpcode, this, qi::_1)])
												>>qi::lit(';');
				functionName = qi::as_string[+(qi::alpha|'_')>> *(qi::alnum|'_')]
								[phx::bind(&RulesGrammar::SetFunctionName, this, qi::_1)];
								
				param = (qi::as_string[+(qi::alpha|'_')>> *(qi::alnum|'_')]
						[phx::bind(&RulesGrammar::ParamToVect, this, qi::_1)]);
				
				call_function = functionName >> qi::char_('(')>> -(give_param % ',')>>qi::lit(')')
											[boost::bind(&RulesGrammar::FuncReview, this)];
				
				give_param = (int_p | name
										[boost::bind(&RulesGrammar::GivetheParams, this, 0x01B2)]
										[boost::bind(&RulesGrammar::SetTempName,this)]
										[boost::bind(&RulesGrammar::GiveAddrParam,this)]
									) [boost::bind(&RulesGrammar::IncreaseParam,this)]; 
				
				int_p = (int_[boost::bind(&RulesGrammar::GivetheParams, this, 0x01B1)]
							[phx::bind(&RulesGrammar::GivetheParams, this, qi::_1)] | 
						double_[boost::bind(&RulesGrammar::GivetheParams, this, 0x01B1)]
							[phx::bind(&RulesGrammar::GivetheParams, this, qi::_1)]); 
				
				//программа начинается с объявления переменных, либо есть, либо нет				
				programm = -(qi::lit("var")>>variable>>*(','>>variable) >> ';')>>start_prog;
				//объявление переменной + возможная инициализация
				variable = (name[boost::bind(&RulesGrammar::PushOpcode, this, 0x00AB)]
								[boost::bind(&RulesGrammar::PushVar, this)]
								[boost::bind(&RulesGrammar::PushOpcode, this, 1)]
								[boost::bind(&RulesGrammar::PushOpcode, this, 0)]
								>> -(init));
								//[boost::bind(&RulesGrammar::PushVarNum, this)];
				//операция присваивания
				associate = (qi::char_('=') >> (call_function 
												[boost::bind(&RulesGrammar::PushOpcode, this, 0x3001)]
												[boost::bind(&RulesGrammar::PushBuffAddr, this)]
												[boost::bind(&RulesGrammar::PushOpcode, this, 0x01B7)]
												|
												expression
												[boost::bind(&RulesGrammar::Resolve, this)]
												[boost::bind(&RulesGrammar::PushOpcode, this, 0x3001)]
												[boost::bind(&RulesGrammar::PushBuffAddr, this)]
												[boost::bind(&RulesGrammar::PushOpcode, this, 0x00AA)]
												));
				assoc = (qi::lit('=')>> (name 
										[boost::bind(&RulesGrammar::PushOpcode, this, 0x3000)]
										[boost::bind(&RulesGrammar::PushBuffAddr, this)]
										[boost::bind(&RulesGrammar::SetBuffName, this)]
										[boost::bind(&RulesGrammar::PushBuffAddr, this)] |
										int_ [boost::bind(&RulesGrammar::PushOpcode, this, 0x3001)]
											[phx::bind(&RulesGrammar::PushOpcode, this, qi::_1)]));
				//инициализация
				init = qi::char_('=') >> binding;
				//определение инициалзируемого значения
				binding = ( uint_bind|double_bind |qi::lit('"') 
								[boost::bind(&RulesGrammar::TakeStack, this, 0x00AC)]
							>> strings
											//[boost::bind(&RulesGrammar::Increase, this)]
											>>'"');
				//беззнаковое целое
				uint_bind = int_[boost::bind(&RulesGrammar::TakeStack, this, 0x00AB)]
							[boost::bind(&RulesGrammar::PushOpcode, this, this->v.var_num)]
							[phx::bind(&RulesGrammar::PushOpcode, this, qi::_1)];
				//дробное 
				double_bind = double_[boost::bind(&RulesGrammar::TakeStack, this, 0x00AB)]
							[boost::bind(&RulesGrammar::PushOpcode, this, this->v.var_num)]
							[phx::bind(&RulesGrammar::PushOpcode, this, qi::_1)];
				//имя переменной
				name = qi::as_string[+(qi::alpha|'_')>> *(qi::alnum|'_')]
						[phx::bind(&RulesGrammar::SetName, this, qi::_1)]; 

				//виды возможных команд
				//условия, математические операции, операции вывода
				start_prog = *((condition | stream |operations | call_function >>';'));
				//строковое значение
				strings = qi::as_string[lexeme[*(qi::char_ - qi::char_('"'))]]
								[phx::bind(&RulesGrammar::Convert, this, qi::_1)];
								//[boost::bind(&RulesGrammar::PushValue, this)];
				//операция вывода
				stream = qi::lit("out")
						>> (name[boost::bind(&RulesGrammar::PushOpcode, this, 0x00C8)]
								[boost::bind(&RulesGrammar::SetBuffName, this)] 
								[boost::bind(&RulesGrammar::PushBuffAddr, this)]
							| int_[boost::bind(&RulesGrammar::PushOpcode, this, 0x00C9)]
									[phx::bind(&RulesGrammar::PushOpcode, this, qi::_1)]
										//[boost::bind(&RulesGrammar::PushValue, this)] 
							| double_[boost::bind(&RulesGrammar::PushOpcode, this, 0x00C9)]
									[phx::bind(&RulesGrammar::PushOpcode, this, qi::_1)]
									//	[boost::bind(&RulesGrammar::PushValue, this)]  
							| (qi::lit('"')[boost::bind(&RulesGrammar::PushOpcode, this, 0x00CA)]
							>> strings
								>>'"') )
						  >> ';';
				//математические операции
				operations = name [boost::bind(&RulesGrammar::SetBuffName, this)] >> (associate | assoc) >>';';
				//условия
				condition = qi::lit("if")>>'('>>cond>>')'>>qi::char_('{')>>start_prog >> '}';
				//условные выражения
				cond = name >> ((('>'|qi::lit(">=")|'<'|qi::lit("<="))>>(int_|double_))|"==">>(int_|double_|('"'>>*(qi::char_)>>'"'))); 
				//парсинг математических выражений
				expression = term [boost::bind(&RulesGrammar::CheckSetTerm, this,1)]  >> 
							*((qi::char_('-') >> term[boost::bind(&RulesGrammar::CheckSetTerm, this,2)])
									[boost::bind(&RulesGrammar::SetSign, this, 1,2)]
									[boost::bind(&RulesGrammar::SetFlag, this,0)]  
									[boost::bind(&RulesGrammar::CheckSetTerm, this,1)]
									[boost::bind(&RulesGrammar::CheckAndSetOpcodeTerm, this)]
							| (qi::char_('+') >> term [boost::bind(&RulesGrammar::CheckSetTerm, this, 2)]) 
									[boost::bind(&RulesGrammar::SetSign, this, 0,2)]
									[boost::bind(&RulesGrammar::SetFlag, this,0)]
									[boost::bind(&RulesGrammar::CheckSetTerm, this,1)]
									[boost::bind(&RulesGrammar::CheckAndSetOpcodeTerm, this)]);
                //обработка умножения и деления
				term       =  factor[boost::bind(&RulesGrammar::CheckSetFactor, this,1)]
									>> 
							*( ('*' >> factor[boost::bind(&RulesGrammar::CheckSetFactor, this,2)])
										[boost::bind(&RulesGrammar::SetSign, this, 2,1)] 
										[boost::bind(&RulesGrammar::SetFlag, this,0)]

							| ('/' >> factor[boost::bind(&RulesGrammar::CheckSetFactor, this,2)] )
										[boost::bind(&RulesGrammar::SetSign, this, 3,1)]
										[boost::bind(&RulesGrammar::SetFlag, this,0)]);
										
				factor     = (name[boost::bind(&RulesGrammar::PushName, this)]
									[boost::bind(&RulesGrammar::SetBuffFlag, this, 1)]
							| qi::uint_[phx::bind(&RulesGrammar::SetMath, this, qi::_1)]
                           |  '(' >> expression >> ')' );
		}
		//установка числового значения
		void SetNum(int i){
			num =i;
		}
		void PushFuncVars(){
			vector<size_opcode>::iterator funcIt = find(opcodes.begin(), opcodes.end(), f.funcId);
			opcodes.at(funcIt - opcodes.begin()+2) = func_v.size();
		}
		void PushCodeSize(){
			vector<size_opcode>::iterator funcBeg = find(opcodes.begin(), opcodes.end(), f.funcId);
			opcodes.at(funcBeg - opcodes.begin()+3) = (opcodes.end()-funcBeg-4)*sizeof(size_opcode);
			f.func_param.clear();
			func_v.clear();
		}
		void GivetheParams(size_opcode par){
			params.push_back(par);
		}
		void SetTempName(){
			v.temp_name = v.name;
			v.temp_addr = FindVarVal(v.temp_name);
		}
		void GiveAddrParam(){
			params.push_back(v.temp_addr);
		}
		void PushParam(){
			serv.param_num = f.func_param.size();
			PushOpcode(serv.param_num);
			function_list.push_back(serv);
			PushOpcode(0);
			PushOpcode(0);
			f.param = 0;
		} 
		
		void FuncReview(){
			vector<func_service>::iterator beg = function_list.begin(), end = function_list.end();
			vector<size_opcode>::iterator it = params.begin(), end_p = params.end();
			while(beg!=end){
				cout << "~~~ "<<f.func_name<<" ~~~"<<endl;
				if((*beg).name == f.func_name){
					cout << "~~~ "<< (*beg).name<<" ~~~"<<endl;
					cout << "params "<< f.param<<" ~~~"<<endl;
					if((*beg).param_num == f.param){
						
						PushOpcode(0x01B6);
						PushOpcode(f.param);
						while(it!=end_p){
							PushOpcode((*it));
							it++;
						}
						PushOpcode((*beg).addr);
						f.param = 0;
						break;
					}
				}
				beg++;
			}
			params.clear();
			
		}
		
		void SetVarStack(int i){
			var_stack.push_back(i);
		}
		
		void ParamToVect(str_t p){
			f.func_param.push_back(p);
		}
		
		void Increase(){
			v.var_num++;
		}
		void IncreaseParam(){
			f.param++;
		}
		void PushVarNum(){
			int i = opcodes.size();
			opcodes.at(i-v.var_num-1) = v.var_num;
			v.var_num = 1;
		}
		
		void TakeStack(int fl){
			opcodes.pop_back();
			opcodes.pop_back();
			opcodes.pop_back();
			PushOpcode(fl);
		}
		
		void ClearStack(){
			var_stack.clear();
		}
		void PushStr(){
			
		}
		void FinalPushStr(){
			
			
		}
			
		std::wstring utf8_to_wstring(const std::string& str)
		{
			return utf_to_utf<wchar_t>(str.c_str(), str.c_str() + str.size());
		}
		std::string wstring_to_utf8(const std::wstring& str)
		{
			return utf_to_utf<char>(str.c_str(), str.c_str() + str.size());
		}  
		void Convert(std::string str){
					wstring st = utf8_to_wstring(str);
					wstring::iterator beg = st.begin(), end = st.end();
					int count = end - beg;
					int temp, temp_c = count;
					//cout<<count<<endl;
					opcodes.push_back(count);
					while(beg!=end){
						temp = (short int)(*beg);
						temp_c--;
						temp <<= 16;
						//cout<<std::hex<<temp<<endl;	
						if(count%2==1){
							if(temp_c!=0){
							beg++;
							temp^=(short int)(*(beg));
							//cout<<std::hex<<temp<<endl;	
							PushOpcode(temp);
							//<<std::hex<<opcodes.back()<<endl;
							temp=0;
							temp_c--;
							}
							else{
								PushOpcode(temp);
							}
						}
						else if(count%2==0){
							beg++;
							temp^=(short int)(*(beg));
							PushOpcode(temp);
							//cout<<std::hex<<opcodes.back()<<endl;
							temp=0;
							temp_c--;
						}
						beg++;
					}
					wcout << st << endl;
			}
		//установка типа
		void SetType(int i){
			v.funcType =i;
			cout<<v.funcType<<endl;
		}
		int GetType(){
			return v.funcType;
			//cout<<v.funcType<<endl;
		}
		//установка имени переменной
		void SetName(str_t name){
			v.name = name;
			//cout<<"name: "<<v.name<<endl;
		}
		void SetFunctionName(str_t name){
			f.func_name = name;
		}
		void SetFuncProperty(){
			f.func_num++;
			f.funcId = 0x00A1 + 0x0100*(f.func_num);
			PushOpcode(f.funcId);
			f.addr = (4 + opcodes.size()-1)*sizeof(size_opcode);
			serv.addr = f.addr;
			serv.name = f.func_name;
			//cout<<"~~~ "<<f.addr<<" ~~~"<<endl;
			//function_list.insert(pair<str_t,int>(f.func_name, f.addr));
			
		}
		//установка флага переменная-число
		void SetFlag(int val){
			var_flag = val;
		}
		void SetBuffFlag(int val){
			buff_flag = val;
		}
		//установка адреса переменной
		void SetAddr(int address){
			v.addr = address;
		}
		
		void SetBuffName(){
			v.name_buff = v.name;
			//cout<<"my var "<<v.name_buff<<endl;
			v.buff_addr = FindVarVal(v.name_buff);
			//cout<<"my addr "<<v.buff_addr<<endl;
		}
		void PushBuffAddr(){
					opcodes.push_back(v.buff_addr);
		}
		
		void SetOp(vector<int> opcode){
			opcodes = opcode;
		}
		//запись в вектор обратной польской записи числового значения
		void SetMath(int val){
			SetFlag(0);
			math_reverse_form.push_back(val);
			//cout<<"=========================="<<endl;
			//cout<<math_reverse_form.back()<<endl;
		}
		//установка опкодов математических операций
		void SetSignStruct(int plus, int minus, int multi, int div){
			s.PLUS = plus;
			s.MINUS = minus;
			s.MULTI = multi;
			s.DIV = div;
		}
		//запись в вектор ОПЗ опкодов мат.операций
		void SetSign(int op_sign, int f){
			switch(f){
				case 1:
					CheckAndSetOpcodeFactor();
					break;
				case 2:
					CheckAndSetOpcodeTerm();
					break;
			}
			switch(op_sign){
				case 0:
					math_reverse_form.push_back(s.PLUS);
					break;
				case 1:
					math_reverse_form.push_back(s.MINUS);
					break;
				case 2:
					math_reverse_form.push_back(s.MULTI);
					break;
				case 3:
					math_reverse_form.push_back(s.DIV);
					break;
			}
			//cout<<"=========================="<<endl;
			//cout<<math_reverse_form.back()<<endl;
		}
		
		//доступ к словарю переменных
		map<str_t, int> GetVar(){
			return var_v;
		}
		//доступ к вектору опкодов
		vector <size_opcode> GetOp(){
			return opcodes;
		}
		//Доступ к вектору ОПЗ
		vector<int> GetMath(){
			return math_reverse_form;
		}
		//проверка номера операнда и определения типа (переменная или число) по флагу
		void CheckSetTerm(int num){
			//cout<<"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"<<endl;
			//cout<< var_flag<<endl;
			switch(num){
				case 1:
					op_term.first = var_flag;
					break;
				case 2:
					op_term.second = var_flag;
					break;
			}
			//var_flag = 0;
		}
		void CheckSetFactor(int num){
			//cout<<"######################"<<endl;
			//cout<< var_flag<<endl;
			switch(num){
				case 1:
					op_factor.first = var_flag;
					break;
				case 2:
					op_factor.second = var_flag;
					break;
			}
		}
		//установка опкодов мат.операций в зависимости от операндов
		void CheckAndSetOpcodeTerm(){
			if(op_term.first==0){
				if(op_term.second==0){
					SetSignStruct(0x1003,0x1007,0x100B,0x100F);
				}
				else{
					SetSignStruct(0x1002,0x1006,0x100A,0x100E);
				}
			}
			else{
				if(op_term.second==0){
					SetSignStruct(0x1001,0x1005,0x1009,0x100D);
				}
				else{
					SetSignStruct(0x1000,0x1004,0x1008,0x100C);
				}				
			}
		}
		void CheckAndSetOpcodeFactor(){
			if(op_factor.first==0){
				if(op_factor.second==0){
					SetSignStruct(0x1003,0x1007,0x100B,0x100F);
				}
				else{
					SetSignStruct(0x1002,0x1006,0x100A,0x100E);
				}
			}
			else{
				if(op_factor.second==0){
					SetSignStruct(0x1001,0x1005,0x1009,0x100D);
				}
				else{
					SetSignStruct(0x1000,0x1004,0x1008,0x100C);
				}				
			}
		}
		//ахождение адреса переменной
		int FindVarVal(str_t val){
			auto map<str_t,int>::iterator it, end;
			vector<str_t>::iterator it_param, begin, par_end;
			switch(v.funcType){
				case 0:
					it = var_v.find(val);
					end = var_v.end();
					break;
				case 1:
					it = func_v.find(val);
					end = func_v.end();
					par_end = f.func_param.end();
					begin = f.func_param.begin();
					it_param = find(begin, par_end, val);
					break;
			}
			if(it != end){
				//cout<<"~~~ "<<it->second<<" ~~~"<<endl;
				return (it->second);
				}
			else if(it_param!=par_end){
				//PushOpcode(0x3000);
				//PushOpcode(0x00AF);
				
				int paramNum = it_param - begin+1;
				//PushOpcode(0x00B0+paramNum);
				//math_reverse_form.push_back(0x00AF);
				
				//math_reverse_form.push_back(0x00B3);
				return 0x188A0+paramNum;
				//PushOpcode(paramNum);
			}
			else{
				return -1;
			}
		}
		//запись адреса переменной в вектор опкодов
//		void PushAddr(std::string val){
//					opcodes.push_back(FindVarVal(val));
//					//opcodes.push_back(FindVarVal(val));
//		}
		//запись опкода в вектор
		void PushOpcode(int opcode){
			opcodes.push_back(opcode);			
		}
		//
//		void PushOperation(){
//			while(math_reverse_form.size()!=0){
//				opcodes.push_back(math_reverse_form.back());	
//				cout<<std::hex<<"take param:  "<<math_reverse_form.back()<<endl;
//				math_reverse_form.pop_back();	
//			}
//		}
		//установка флага переменная-число и запись адреса в вектор с ОПЗ
		void PushName(){
			SetFlag(1);
			switch(v.funcType){
				case 0:
					math_reverse_form.push_back(FindVarVal(v.name));	
					//opcodes.push_back(v.buff_addr);
			//		opcodes.push_back(FindVarVal(val));
					break;
				case 1:
					math_reverse_form.push_back(FindVarVal(v.name));	
					//FindVarVal(v.name_buff);
					break;
			}
			//int index = FindVarVal(v.name)/sizeof(size_opcode) - 3;
			//cout<<"=========================="<<endl;
			//cout<<math_reverse_form.back()<<endl;
		}

		//запись в вектор опкодов числа
		void PushValue(){
			opcodes.push_back(num);
			num = 0;
		}	
		//добавление в словарь записи типа Имя_переменной, адрес
		void PushVar()
		{
			cout<<"===== "<<v.funcType<<" ======="<<endl;
			int addr = (4 + opcodes.size()-1)*sizeof(size_opcode);
			SetAddr(addr);
			cout<<v.name<<" "<<v.addr<<endl;
			switch(v.funcType){
					case 0:
						var_v.insert(pair<str_t,int>(v.name, v.addr));
						break;
					case 1:
						func_v.insert(pair<str_t,int>(v.name, v.addr));
						break;
			}
		}
		void Resolve(){
			int a,i=0;
			vector<int>::iterator it = math_reverse_form.begin();
			while(it!=math_reverse_form.end()){
				//cout<<std::hex<<(*it)<< " ";
				if(CheckOperation((*it))){
					stack.push_back((*it));
					it++;
				}
				else if(*it == 0x00AF){
						
				}
				else{
					//if(i==0){
						PushOpcode((*it));
						a = stack.back();
						stack.pop_back();
						if(stack.back()==0x00AA && a==0x00AA){
							PushOpcode(0x00A9);
						}
						else{
							PushOpcode(stack.back());
						}
						PushOpcode(a);
						stack.pop_back();
						stack.push_back(0x00AA);
						it++;
						i++;
					
				}
			}
			//cout<<"~~~~~~~ "<<FindVarVal(v.name_buff)<<" ~~~~~~~~"<<endl;
			math_reverse_form.clear();
		}
		bool CheckOperation(int val){
			if(val!=0x1000 && val!=0x1001 && val!=0x1002 && val!=0x1003 && val!=0x1004 && val!=0x1005&&val!=0x1006&&val!=0x1007&&val!=0x1008&&val!=0x1009&&val!=0x100A&&val!=0x100B&&val!=0x100C&&val!=0x100D&&val!=0x100E&&val!=0x100F){
				return true;
			}
			else{
				return false;
			}
		}
		
	};
}
#endif 