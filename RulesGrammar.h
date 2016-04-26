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
		//вектор опкодов математического выражения в обратной польской записи		
		vector<int> math_reverse_form;
		//объявление правил
		qi::rule<Iterator, qi::space_type> start_programm, programm, name, variable, associate, binding, uint_bind, double_bind,expression, term,factor,cond, start_prog, condition, operations, stream, init,id,strings;

	public:
		RulesGrammar() : RulesGrammar::base_type(start_programm)
		{
				//начало программы
				start_programm = qi::lit("start")[boost::bind(&RulesGrammar::PushOpcode, this, 0x00A1)] 
								>>'('>>qi::char_(')')>>qi::char_('{')>>programm>>'}';
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
				associate = (qi::char_('=') >> (expression
												[boost::bind(&RulesGrammar::Resolve, this)]
												[boost::bind(&RulesGrammar::PushOpcode, this, 0x3001)]
												[boost::bind(&RulesGrammar::PushBuffAddr, this)]
												[boost::bind(&RulesGrammar::PushOpcode, this, 0x00AA)] | 
												name 
												[boost::bind(&RulesGrammar::PushOpcode, this, 0x3000)]
												[boost::bind(&RulesGrammar::PushBuffAddr, this)]
												[boost::bind(&RulesGrammar::SetBuffName, this)]
												[boost::bind(&RulesGrammar::PushBuffAddr, this)]
												));
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
				start_prog = *((condition | stream|operations));
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
				operations = name [boost::bind(&RulesGrammar::SetBuffName, this)] >> associate >>';';
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
		void SetVarStack(int i){
			var_stack.push_back(i);
		}
		
		void Increase(){
			v.var_num++;
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
//			switch(CODE){
//				case 0:
////					wstring wsstr;
////					StringToWString(ws,str);
////					wcout<<wsstr<<endl;
//					break;
//				case 1:
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
							cout<<std::hex<<temp<<endl;	
							PushOpcode(temp);
							cout<<std::hex<<opcodes.back()<<endl;
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
							cout<<std::hex<<opcodes.back()<<endl;
							temp=0;
							temp_c--;
						}
						beg++;
					}
					wcout << st << endl;
			}
		//}
		//установка типа
//		void SetType(int i){
//			v.type =i;
//		}
		//установка имени переменной
		void SetName(str_t name){
			v.name = name;
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
			v.buff_addr = FindVarVal(v.name_buff);
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
			cout<<"=========================="<<endl;
			cout<<math_reverse_form.back()<<endl;
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
			cout<<"=========================="<<endl;
			cout<<math_reverse_form.back()<<endl;
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
			cout<<"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"<<endl;
			cout<< var_flag<<endl;
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
			cout<<"######################"<<endl;
			cout<< var_flag<<endl;
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
			auto map<str_t,int>::iterator it = var_v.find(val);
			if(it != var_v.end()){
				return (it->second);
				}
			else{
				return -1;
			}
		}
		//запись адреса переменной в вектор опкодов
		void PushAddr(std::string val){
			opcodes.push_back(FindVarVal(val));
		}
		//запись опкода в вектор
		void PushOpcode(int opcode){
			opcodes.push_back(opcode);			
		}
		//
		void PushOperation(){
			while(math_reverse_form.size()!=0){
				opcodes.push_back(math_reverse_form.back());	
				math_reverse_form.pop_back();	
			}
		}
		//установка флага переменная-число и запись адреса в вектор с ОПЗ
		void PushName(){
			SetFlag(1);
			//int index = FindVarVal(v.name)/sizeof(size_opcode) - 3;
			math_reverse_form.push_back(FindVarVal(v.name));	
			cout<<"=========================="<<endl;
			cout<<math_reverse_form.back()<<endl;
		}

		//запись в вектор опкодов числа
		void PushValue(){
			opcodes.push_back(num);
			num = 0;
		}	
		//добавление в словарь записи типа Имя_переменной, адрес
		void PushVar()
		{
			int addr = (4 + opcodes.size()-1)*sizeof(size_opcode);
			SetAddr(addr);
			var_v.insert(pair<str_t,int>(v.name, v.addr));
		}
		void Resolve(){
			int a,i=0;
			vector<int>::iterator it = math_reverse_form.begin();
			while(it!=math_reverse_form.end()){
				cout<<std::hex<<(*it)<< " ";
				if(CheckOperation((*it))){
					stack.push_back((*it));
					it++;
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
			cout<<"~~~~~~~ "<<FindVarVal(v.name_buff)<<" ~~~~~~~~"<<endl;
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