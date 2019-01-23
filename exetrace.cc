#include "cpu/exetrace.hh"

#include <iomanip>

#include "arch/isa_traits.hh"
#include "arch/utility.hh"
#include "base/loader/symtab.hh"
#include "cpu/o3/fetch.hh"
#include "cpu/o3/fetch.cc"
#include "config/the_isa.hh"
#include "cpu/base.hh"
#include "cpu/static_inst.hh"
#include "cpu/thread_context.hh"
#include "debug/ExecAll.hh"
#include "debug/SIMDFLAG.hh"
#include "debug/STATFLAG.hh"
#include "enums/OpClass.hh"
#include <string>
#include <iostream>
#include <sstream>
#include <iterator>
#include <fstream>
#define TAMARRAY 16
#define CACHESIZE 16


//VARIAVEIS TIAGO

/*
typedef struct {
    Addr DataAddress, PC;
    int regorigem;
    
    bool regdirty, regreused, adrloaded;
} Store;

//Variaveis exclusivos de cada funcao
typedef struct {
    std::string Funct="";
    
    bool branch, branchincond, compconst, possibleLoop;
    
    int regvar, contstores;
    int previsao;
    
    Addr PCAnterior, PCofLastBranch, PClastincondbranch, PCofLastFunctChange;
    
    Reg regcontent[16];
    Store storebuffer[MEM];
} FunctionInfo;

FunctionInfo F[MEM];
Addr PC;


typedef struct {
    long long int data;
    
    bool comparacao;
    int  constlastinc;
    Addr PClastinc;
    std::string instinc;
} Reg;
*/


typedef struct {
    long long int data;
    int rd1,rd2, rs1,rs2,rs3,rs4;
} InstReg;

InstReg InstRegs;
InstReg PrevRegs;


typedef struct {
    Addr firstAddress, lastAddress, storeInstAddress, storeDataAddress;

    int executions, iterations, storeRegister, storeDataSize;
    long long int predictedSize, sequentialExecTime, iterationTimeSimd, detectionLatency;
    
    bool analyzed, discarded, vectorizable, definedSize;
} LoopInfo;

LoopInfo loops[CACHESIZE];


typedef struct {
    std::string instType;
    int simdLatency;
    long long int cont;
    long long int simdCont;
} InstLat;

InstLat InstLatency[12];


typedef struct {
    Addr cmpsAddress;
    long long int cmpsOp1, cmpsOp2;
    long long int iterationTimeSimd;
    
    bool enable;
} LoopAnalyze;

LoopAnalyze LoopAnalysis;


bool inicialization=1, printResults=1;
bool instCond, instSetFlag, instCmp, instBranchSubRoutine, instMicro, thereIsConstant;
bool possibleLoop=0;

long long int ticks_sequential = 0, ticks_parallel = 0;
long long int ticks_sequential_indef = 0, ticks_parallel_indef = 0;

short int i, j, k, f, simdExecution, currentLoop=0; 
long long int detectionLatency=0, totalticksvetorizados=0, totalticksvetorizados_indef=0;
long long int constante, loop_def=0, loop_indef=0, loop_cond=0, loop_funct=0;


Addr instAddress, prevInstAddress, dataAddress, regContent[32];

std::string instruction, prevInst, instType, prevInstType;


Addr programCounter;
std::string funct, previousFunct;



//VARIAVEIS JORDAN

const int n = 800;
const int column_number = 18;
const int line_number = 5;
const int mem_line = 2;
const int reg_per_cycle = 4;
const int period = 100;

struct arrayMap{
   Addr afterbranchId;
   int registersMap[16];
   int arrayMatrix[line_number][column_number];
};

struct arrayMemory{
   Addr afterbranchId;
   Addr lastID;
   int arrayMatrix[line_number][column_number];
   bool readReg[16];
   bool writeReg[16];
   long long int inTick;
   long long int finTick;
   long long int configCycles;
   int specDeep;
   long long int accesses;
   struct arrayMemory *next;
};

arrayMap arrMap;

arrayMemory *memoriaConfig = new arrayMemory[n];

//STATISTICS FLAGS
long long int economiaTotal = 0;
long long int totalHits= 0;
long long int totalcontBlocks = 0;
long long int totalConfigs = 0;
long long int totalInst = 0;
long long int totalCond = 0;
long long int totalALU = 0;
long long int totalMEM = 0;
long long int totalOther = 0;
long long int totalTick = 0;

int firsttime = 0, loopVerifier = 0, depAlloc = 0, endArray = 0, specDeep = 0, indice_menor = 0, init_conf = 0, decreaseCycle = 0;
int configurationHit = 0, initArray = 0, difTick = 0, auxinTick = 0, auxfinTick = 0, oneConfigCycles = 0, inTick = 0;
int finTick = 0, totalCycles = 0, arrayCycle = 0, greatIndividualEconomy = 0, index_hit = 0, flagCount = 0;
int condinstCount = 0, branchInstruction = 0, previousWasBranch = 0, configStart = 0, arrayFull = 0, conditionalInstruction = 0;
bool regRead[16], regWrite[16], specregRead[16], specregWrite[16], contregRead[16], contregWrite[16];
Addr lastID = 0, savlastID = 0;
int contadorWb = 0, contadorSr = 0, wbCycles = 0, srCycles = 0;
bool executaILP = 0;
int executionLoopID;
Addr addrendDLP = 0;


struct node
{
   long long int data;
   int rd1,rd2, rs1,rs2,rs3,rs4;
};

node temp;


using namespace std;
using namespace TheISA;


namespace Trace {

void
ExeTracerRecord::dumpTicks(ostream &outs)
{
    ccprintf(outs, "%7d: ", when);
}

void getReg(const StaticInstPtr &inst, int f, long long int dado, int sel)
{
    int flagCount = 0;
    int index = 0;

    //Verificacao dos registradores fontes e destinos
    while(index < inst->numDestRegs()){ 
        if(inst->destRegIdx(index).isCCReg()){
            flagCount = flagCount + 1;
        }
        else if(!inst->destRegIdx(index).isCCReg() && (index==0)){
            //DPRINTF(SIMDFLAG, "Dest Reg 1: %d\n", inst->destRegIdx(index).index());
            if (sel == 1){
                InstRegs.rd1 = inst->destRegIdx(index).index();
                regContent[inst->destRegIdx(index).index()] = dado;
            }
            else{
                regWrite[inst->destRegIdx(index).index()] = 1;
                temp.rd1 = inst->destRegIdx(index).index();
            }

        }
        else if(!inst->destRegIdx(index).isCCReg() && (index==1)){              
            //DPRINTF(SIMDFLAG, "Dest Reg 2: %d\n", inst->destRegIdx(index).index());
            if(sel == 1){ 
               InstRegs.rd2 = inst->destRegIdx(index).index();
               regContent[inst->destRegIdx(index).index()] = dado;
            }
            else{
               regWrite[inst->destRegIdx(index).index()] = 1;
               temp.rd2 = inst->destRegIdx(index).index();
            }
        }
        else{ 
            //DPRINTF(SIMDFLAG, "REGISTRADOR IGNORADO");            
        }            
        index = index + 1; 
    }

    flagCount = 0;
    index = 0;

    while(index < inst->numSrcRegs()){
        if(inst->srcRegIdx(index).isCCReg() || inst->srcRegIdx(index).isMiscReg()){
            flagCount = flagCount + 1;              
        }
        else if(!inst->srcRegIdx(index).isCCReg() && !inst->srcRegIdx(index).isMiscReg() && ((index-flagCount)==0)){
            if(sel == 1){
                InstRegs.rs1 = inst->srcRegIdx(index).index();
            }
            else{
                temp.rs1 = inst->srcRegIdx(index).index();
                regRead[inst->srcRegIdx(index).index()] = 1;
            }
            //DPRINTF(SIMDFLAG, "Source Reg 1: %d\n", inst->srcRegIdx(index).index());
        }
        else if(!inst->srcRegIdx(index).isCCReg() && !inst->srcRegIdx(index).isMiscReg() && ((index-flagCount)==1)){
            if(sel == 1){
                InstRegs.rs2 = inst->srcRegIdx(index).index();
            }
            else{
                temp.rs2 = inst->srcRegIdx(index).index();
                regRead[inst->srcRegIdx(index).index()] = 1;
            }
            //DPRINTF(SIMDFLAG, "Source Reg 2: %d\n", inst->srcRegIdx(index).index());  
        }
        else if(!inst->srcRegIdx(index).isCCReg() && !inst->srcRegIdx(index).isMiscReg() && ((index-flagCount)==2)){
            if(sel == 1){
                InstRegs.rs3 = inst->srcRegIdx(index).index();
            }
            else{
                temp.rs3 = inst->srcRegIdx(index).index();
                regRead[inst->srcRegIdx(index).index()] = 1;
            }
            //DPRINTF(SIMDFLAG, "Source Reg 3: %d\n", inst->srcRegIdx(index).index());  
        }
        else if(!inst->srcRegIdx(index).isCCReg() && !inst->srcRegIdx(index).isMiscReg() && ((index-flagCount)==3)){
            if(sel == 1){
               InstRegs.rs4 = inst->srcRegIdx(index).index();            
            }
            else{
               temp.rs4 = inst->srcRegIdx(index).index();
               regRead[inst->srcRegIdx(index).index()] = 1;
            }
            //DPRINTF(SIMDFLAG, "Source Reg 4: %d\n", inst->srcRegIdx(index).index());  
        }
        else{
            //DPRINTF(SIMDFLAG, "REGISTRADOR IGNORADO");                
        }

        index = index + 1;
    }

}

//long long int impressao=1000000000;

//PRINTA O TRACE
void Trace::ExeTracerRecord::traceInst(const StaticInstPtr &inst, bool ran)
{
    //imprimeTracePadrao(inst, ran);
    
    //calculaEconomiaVetorial(inst, ran);
    
    /* DEBUG
    if(when > 7118000000 && when < 7119240000){
        imprimeTracePadrao(inst, ran);
        calculaEconomiaVetorial(inst, ran);
    }
    //*/


    //outs << "EXECUTA ILP:   " << executaILP << "\n";
    //if(!executaILP)
        //calculaEconomia(inst);
}

void Trace::ExeTracerRecord::calculaEconomiaVetorial(const StaticInstPtr &inst, bool ran)
{
    inicializaVariaveis(inst, ran);
    extraiDadosDoTrace(inst, ran);
    analisaLoops(inst, ran);
}


void Trace::ExeTracerRecord::imprimeTracePadrao(const StaticInstPtr &inst, bool ran){
    std::string sym_str;
    Addr sym_addr;
    Addr cur_pc = pc.instAddr();
    ostream &outs = Trace::output();
    
    if (Debug::ExecTicks)
        dumpTicks(outs);
    
    outs << thread->getCpuPtr()->name() << " ";

    if (Debug::ExecAsid)
        outs << "A" << dec << TheISA::getExecutingAsid(thread) << " ";

    if (Debug::ExecThread)
        outs << "T" << thread->threadId() << " : ";
        

    outs << pc.instAddr() << "\t";
    
    
    if (debugSymbolTable && Debug::ExecSymbol &&
            (!FullSystem || !inUserMode(thread)) &&
            debugSymbolTable->findNearestSymbol(cur_pc, sym_str, sym_addr)) {
        if (cur_pc != sym_addr)
            sym_str += csprintf("+%d", cur_pc - sym_addr);
        outs << "@" << sym_str;
    } 
    else {
        outs << "0x" << hex << cur_pc;
    }


    outs << " : ";

    //
    //  Print decoded instruction
    //

    outs << setw(26) << left;
    outs << inst->disassemble(cur_pc, debugSymbolTable);
    
    if (ran) {
        outs << " : ";

        if (Debug::ExecOpClass)
            outs << Enums::OpClassStrings[inst->opClass()] << " : ";

        if (Debug::ExecResult && !predicate)
            outs << "Predicated False";
        
        if (Debug::ExecResult && data_status != DataInvalid)
            ccprintf(outs, " D=%#018x", data.as_int);

        if (Debug::ExecEffAddr && getMemValid())
            outs << " A=0x" << hex << addr;
        
        if (Debug::ExecFetchSeq && fetch_seq_valid)
            outs << "  FetchSeq=" << dec << fetch_seq;

        if (Debug::ExecCPSeq && cp_seq_valid)
            outs << "  CPSeq=" << dec << cp_seq;

        if (Debug::ExecFlags) {
            outs << "  flags=(";
            inst->printFlags(outs, "|");
            outs << ")";
        }
    }

    
    //  End of line...
    
    outs << endl;
}


void Trace::ExeTracerRecord::inicializaVariaveis(const StaticInstPtr &inst, bool ran){
    
    if(inicialization){
        inicialization=0;
        
        InstLatency[0].instType="MemRead";
        InstLatency[0].simdLatency=0;
        InstLatency[0].cont=0;
        InstLatency[0].simdCont=0;
        InstLatency[1].instType="MemWrite";
        InstLatency[1].simdLatency=0;
        InstLatency[1].cont=0;
        InstLatency[1].simdCont=0;
        InstLatency[2].instType="IntAlu";
        InstLatency[2].simdLatency=4;
        InstLatency[2].cont=0;
        InstLatency[2].simdCont=0;
        InstLatency[3].instType="IntMult";
        InstLatency[3].simdLatency=5;
        InstLatency[3].cont=0;
        InstLatency[3].simdCont=0;
        InstLatency[4].instType="IntDiv";
        InstLatency[4].simdLatency=5;
        InstLatency[4].cont=0;
        InstLatency[4].simdCont=0;
        InstLatency[5].instType="FloatMemRead";
        InstLatency[5].simdLatency=0;
        InstLatency[5].cont=0;
        InstLatency[5].simdCont=0;
        InstLatency[6].instType="FloatMemWrite";
        InstLatency[6].simdLatency=0;
        InstLatency[6].cont=0;
        InstLatency[6].simdCont=0;
        InstLatency[7].instType="FloatAdd";
        InstLatency[7].simdLatency=5;
        InstLatency[7].cont=0;
        InstLatency[7].simdCont=0;
        InstLatency[8].instType="FloatCmp";
        InstLatency[8].simdLatency=3;
        InstLatency[8].cont=0;
        InstLatency[8].simdCont=0;
        InstLatency[9].instType="FloatMult";
        InstLatency[9].simdLatency=3;
        InstLatency[9].cont=0;
        InstLatency[9].simdCont=0;
        InstLatency[10].instType="FloatDiv";
        InstLatency[10].simdLatency=3;
        InstLatency[10].cont=0;
        InstLatency[10].simdCont=0;
        InstLatency[11].instType="FloatSqrt";
        InstLatency[11].simdLatency=9;
        InstLatency[11].cont=0;
        InstLatency[11].simdCont=0;
        
        LoopAnalysis.enable=0;
    }
}

void Trace::ExeTracerRecord::extraiDadosDoTrace(const StaticInstPtr &inst, bool ran){
    
    //ostream &outs = Trace::output();
    std::string sym_str;
    Addr sym_addr;
    Addr cur_pc = pc.instAddr();
    instAddress = pc.instAddr();
    
    previousFunct = funct;

    if (debugSymbolTable && Debug::ExecSymbol &&
            (!FullSystem || !inUserMode(thread)) &&
            debugSymbolTable->findNearestSymbol(cur_pc, sym_str, sym_addr)) {

        funct = sym_str;
        programCounter = cur_pc - sym_addr;
    }
    if (ran) {
        if (Debug::ExecOpClass)
            instType = Enums::OpClassStrings[inst->opClass()];
        if (Debug::ExecEffAddr && getMemValid())
            dataAddress = addr;
    }
    
    //Contador do tipo de instrucao
    for(i=0; i<12; i++){
        if(instType==InstLatency[i].instType){
            if(executaILP){
                if(simdExecution == loops[currentLoop].storeDataSize){
                    InstLatency[i].simdCont++;
                }
            }
            else{
                InstLatency[i].cont++;
            }
            
            break;
        }
    }
    
    //Printa resultados
    if(funct == "_Exit" && printResults){
        printResults=0;
        
        DPRINTF(STATFLAG, "\n");
        DPRINTF(STATFLAG, "ECONOMIA EM LOOPS DEFINIDOS: %d\n", totalticksvetorizados);
        DPRINTF(STATFLAG, "PERCENTUAL DE GANHO VETORIZACAO:    %f %%.\n\n", (100*((float)totalticksvetorizados / (float)when)));
        DPRINTF(STATFLAG, "ECONOMIA EM LOOPS INDEFINIDOS:: %d\n", totalticksvetorizados_indef);
        DPRINTF(STATFLAG, "PERCENTUAL DE GANHO VETORIZACAO INDEF:    %f %%.\n\n\n", (100*((float)totalticksvetorizados_indef / (float)when)));
        
        DPRINTF(STATFLAG, "TOTAL DE TICKS VETORIZADOS DEF: %d\n", ticks_parallel);
        DPRINTF(STATFLAG, "TOTAL DE TICKS SEQUENCIAIS DEF: %d\n", ticks_sequential);
        DPRINTF(STATFLAG, "VETORIZADO DEF / SEQUENCIAL:    %f %%.\n\n", (100*((float)ticks_parallel / (float)ticks_sequential)));
        DPRINTF(STATFLAG, "TOTAL DE TICKS VETORIZADOS INDEF: %d\n", ticks_parallel_indef);
        DPRINTF(STATFLAG, "TOTAL DE TICKS SEQUENCIAIS INDEF: %d\n", ticks_sequential_indef);
        DPRINTF(STATFLAG, "VETORIZADO INDEF / SEQUENCIAL:    %f %%.\n\n", (100*((float)ticks_parallel_indef / (float)ticks_sequential_indef)));
        
        for(i=0; i<CACHESIZE; i++){
            //if(loops[i].vectorizable && loops[i].terminado){
            if(loops[i].vectorizable){
                DPRINTF(STATFLAG, "Loop nº %d\n", i);
            }
        }
        
        DPRINTF(STATFLAG, "\n\n");
        DPRINTF(STATFLAG, "LATENCIA TOTAL DE DETECCAO: %li\n", detectionLatency);
        DPRINTF(STATFLAG, "PERCENTUAL DETECCAO/EXECUCAO:    %f %%.\n\n", (100*((float)detectionLatency / (float)when)));
        
        for(i=0; i<12; i++){
            DPRINTF(STATFLAG, "%s: %li\n", InstLatency[i].instType, InstLatency[i].cont);
            DPRINTF(STATFLAG, "Simd%s: %li\n", InstLatency[i].instType, InstLatency[i].simdCont);
        }
        
        DPRINTF(STATFLAG, "\n");
        DPRINTF(STATFLAG, "Loops definidos: %li\n", loop_def);
        DPRINTF(STATFLAG, "Loops indefinidos: %li\n", loop_indef);
        DPRINTF(STATFLAG, "Loops condicionais: %li\n", loop_cond);
        
        
        //economiaTotal = economiaTotal + totalticksvetorizados;
    }
    
    InstRegs.data = data.as_int;
    InstRegs.rd1 = -1;
    InstRegs.rd2 = -1;
    InstRegs.rs1 = -1;
    InstRegs.rs2 = -1;
    InstRegs.rs3 = -1;
    InstRegs.rs4 = -1;

    long long int dado = data.as_int;
    getReg(inst,f,dado,1);

    //Extracao da instrucao da string
    string buf, word2, word3, word4, word5, word6, cons="";
    stringstream ss(inst->disassemble(cur_pc, debugSymbolTable));
    vector<string> tokens;

    i=1;

    //Separacao das palavras da string
    while (ss >> buf){
        if(i==1)
            instruction=buf;
        if(i==2)
            word2=buf;
        if(i==3)
            word3=buf;
        if(i==4)
            word4=buf;
        if(i==5)
            word5=buf;
        if(i==6)
            word6=buf;

        tokens.push_back(buf);
        i++;
    }


    int instSize=0;

    //Verifica o tamanho da instrucao
    while(instruction[instSize]!='\0')
        instSize++;


    instBranchSubRoutine=0;
    instCond=0;
    instMicro=0;
    instCmp=0;
    instSetFlag=0;

    //Verifica saltos de subrotina
    if(instSize>=2 && instruction[0]=='b' && (instruction[1]=='l' || instruction[1]=='x')){
        instBranchSubRoutine=1;
        //DPRINTF(SIMDFLAG, "branchSubRoutine\n");
    }
    //Verifica instrucoes de condicionais
    else if((instSize>=3) && ((instruction[instSize-2]=='e' && instruction[instSize-1]=='q') ||
                              (instruction[instSize-2]=='n' && instruction[instSize-1]=='e') ||
                              (instruction[instSize-2]=='c' && instruction[instSize-1]=='s') ||
                              (instruction[instSize-2]=='c' && instruction[instSize-1]=='c') ||
                              (instruction[instSize-2]=='m' && instruction[instSize-1]=='i') ||
                              (instruction[instSize-2]=='p' && instruction[instSize-1]=='l') ||
                              (instruction[instSize-2]=='v' && instruction[instSize-1]=='s') ||
                              (instruction[instSize-2]=='v' && instruction[instSize-1]=='c') ||
                              (instruction[instSize-2]=='h' && instruction[instSize-1]=='i') ||
                              (instruction[instSize-2]=='l' && instruction[instSize-1]=='s') ||
                              (instruction[instSize-2]=='g' && instruction[instSize-1]=='e') ||
                              (instruction[instSize-2]=='l' && instruction[instSize-1]=='t') ||
                              (instruction[instSize-2]=='g' && instruction[instSize-1]=='t') ||
                              (instruction[instSize-2]=='l' && instruction[instSize-1]=='e')))
        instCond=1;
    else if(instSize>=3 && instruction[instSize-4]=='_' && instruction[instSize-3]=='u'
                        && instruction[instSize-2]=='o' && instruction[instSize-1]=='p')
        instMicro=1;
    //Verifica instrucao de comparacao
    else if(instruction=="cmps")
        instCmp=1;
    //Verifica instrucoes que setam flags
    else if(instruction[instSize-1]=='s')
        instSetFlag=1;


    thereIsConstant=0;

    //Extracao da constante da string
    if(instCmp){
        if(word2[0]=='#'){
            thereIsConstant=1;
            for (const auto c: word2){
                if(!ispunct(c))
                    cons.push_back(c);
            }
        }
        else if(word3[0]=='#'){
            thereIsConstant=1;
            for (const auto c: word3){
                if(!ispunct(c))
                    cons.push_back(c);
            }
        }
        else if(word4[0]=='#'){
            thereIsConstant=1;
            for (const auto c: word4){
                if(!ispunct(c))
                    cons.push_back(c);
            }
        }
        else if(word5[0]=='#'){
            thereIsConstant=1;
            for (const auto c: word5){
                if(!ispunct(c))
                    cons.push_back(c);
            }
        }
        else if(word6[0]=='#'){
            thereIsConstant=1;
            for (const auto c: word6){
                if(!ispunct(c))
                    cons.push_back(c);
            }
        }
        
        if(thereIsConstant){
            std::istringstream convstrtoint(cons);
            convstrtoint >> constante;
        }
    }
}


void Trace::ExeTracerRecord::analisaLoops(const StaticInstPtr &inst, bool ran){
    bool encontrado=0;
    
    if(possibleLoop){
        possibleLoop=0;
        
        DPRINTF(SIMDFLAG, "possibleLoop\n");
        
        //Branch taken (possivel loop)
        if(instAddress < prevInstAddress){
            DPRINTF(SIMDFLAG, "Branch taken\n");
            
            //Busca loop na cache
            for(i=0; i<CACHESIZE; i++){
                //Loop ID dado pelo endereco da ultima instrucao do loop
                if(loops[i].lastAddress == prevInstAddress){
                    encontrado = 1;   //CACHE HIT
                    loops[i].iterations++;
                    
                    DPRINTF(SIMDFLAG, "LOOP CACHE HIT\n");
                    
                    if(loops[i].discarded){
                        DPRINTF(SIMDFLAG, "LOOP anteriormente descartado\n");
                    }
                    else if(loops[i].analyzed){
                        //Reaproveitamento de loops previamente analisados
                        if(loops[i].vectorizable){
                            if(!executaILP){
                                executaILP = 1;
                                simdExecution = loops[i].storeDataSize;
                                
                                loops[i].sequentialExecTime = when;
                                
                                currentLoop = i;
                                
                                DPRINTF(SIMDFLAG, "Endereco inicial: %#x\n", instAddress);
                                DPRINTF(SIMDFLAG, "Endereco final: %#x\n", prevInstAddress);
                                DPRINTF(SIMDFLAG, "currentLoop: %d\n", currentLoop);
                            }
                            else if(i == currentLoop){
                                simdExecution--;
                                
                                if(simdExecution == 0)
                                    simdExecution = loops[i].storeDataSize;
                            }
                            else{
                                DPRINTF(SIMDFLAG, "WARNING: OUTRO LOOP EM EXECUCAO\n");
                            }
                        }
                        else{
                            DPRINTF(SIMDFLAG, "Loop nao vetorizavel\n");
                        }
                    }
                    else if(loops[i].iterations == 2){
                        //Contabilizacao do tempo de execucao SIMD
                        loops[i].iterationTimeSimd = LoopAnalysis.iterationTimeSimd;
                        
                        DPRINTF(SIMDFLAG, "iterationTimeSimd %d\n", loops[i].iterationTimeSimd);
                        
                        
                        //Logica de previsao de tamanho (inicio)
                        if(LoopAnalysis.cmpsAddress > instAddress && LoopAnalysis.cmpsAddress < prevInstAddress){
                            DPRINTF(SIMDFLAG, "Cmps dentro do range do loop\n");
                            
                            //Cmps dentro do range do loop
                            loops[i].definedSize = 1;
                            loops[i].predictedSize = LoopAnalysis.cmpsOp1;
                            
                            DPRINTF(SIMDFLAG, "loops[%d].predictedSize = %d (cmpsOp1)\n", i, loops[i].predictedSize);
                        }
                        else{
                            DPRINTF(SIMDFLAG, "Loop de tam indefinido\n");
                            
                            //Loop de tam indefinido
                            loops[i].definedSize = 0;
                        }
                    }
                    else if(loops[i].iterations == 3){
                        //Fim da etapa de analise do loop
                        LoopAnalysis.enable = 0;
                        loops[i].analyzed = 1;
                        
                        //Contabilizacao do tempo de analise
                        detectionLatency += when - loops[i].detectionLatency;
                        
                        //Caso falhe a deteccao do tamanho do dado, tamanho padrao = 32 bits
                        if(loops[i].storeDataSize != 8 && loops[i].storeDataSize != 4
                                                       && loops[i].storeDataSize != 2
                                                       && loops[i].storeDataSize != 1){
                            DPRINTF(SIMDFLAG, "Tamanho do dado desconhecido: %d\n", loops[i].storeDataSize);
                            
                            loops[i].storeDataSize = 4;
                        }
                        
                        
                        //Logica de previsao de tamanho (fim)
                        if(loops[i].definedSize){
                            //Calculo da previsao
                            if((LoopAnalysis.cmpsOp1 - loops[i].predictedSize) != 0){
                                loops[i].predictedSize = (LoopAnalysis.cmpsOp2 - LoopAnalysis.cmpsOp1) / (LoopAnalysis.cmpsOp1 - loops[i].predictedSize);
                                loops[i].predictedSize += 3;
                                
                                DPRINTF(SIMDFLAG, "LoopAnalysis.cmpsOp1 = %d\n", LoopAnalysis.cmpsOp1);
                                DPRINTF(SIMDFLAG, "LoopAnalysis.cmpsOp2 = %d\n", LoopAnalysis.cmpsOp2);
                                DPRINTF(SIMDFLAG, "Tamanho previsto %d\n", loops[i].predictedSize);
                                
                                if(loops[i].predictedSize >= 4){
                                    DPRINTF(SIMDFLAG, "Previsao ok\n");
                                    
                                    //Vetorizacao
                                    if(loops[i].vectorizable){
                                        executaILP = 1;
                                        
                                        DPRINTF(SIMDFLAG, "Vetorizavel\n");
                                        
                                        loops[i].sequentialExecTime = when;
                                        
                                        simdExecution = loops[i].storeDataSize;
                                    }
                                }
                                else{
                                    loops[i].definedSize = 0;
                                    
                                    DPRINTF(SIMDFLAG, "Movido para analise de tam indefinido\n");
                                }
                            }
                            else{
                                DPRINTF(SIMDFLAG, "Divisao por zero! op1/op2: %d/%d\n", LoopAnalysis.cmpsOp1, loops[i].predictedSize);
                                
                                loops[i].definedSize = 0;
                            }
                        }
                    }
                    else if(loops[i].executions != 0){
                        //Loop nao analisado na primeira execucao
                        currentLoop = i;
                        
                        LoopAnalysis.enable = 1;
                        LoopAnalysis.iterationTimeSimd = 0;
                        loops[i].predictedSize = 0;
                        loops[i].definedSize = 0;
                        loops[i].analyzed = 0;
                        loops[i].discarded = 0;
                        loops[i].vectorizable = 1;
                        loops[i].storeInstAddress = 0;
                        loops[i].storeDataAddress = 0;
                        loops[i].storeDataSize = 0;
                        loops[i].storeRegister = -1;
                    }
                    
                    break;  //Interrompe busca na cache apos hit
                }
            }
            //CACHE MISS! Registra novo loop
            if(!encontrado){
                encontrado=0;
                
                //Busca enderecos vazios na cache de loops
                for(i=0; i<CACHESIZE; i++){
                    if(!loops[i].analyzed){
                        encontrado=1;
                        currentLoop=i;
                        break;
                    }
                }
                //Politica de substituicao da cache de loops
                if(!encontrado){
                    for(i=0; i<CACHESIZE; i++){
                        if(loops[i].discarded){
                            encontrado=1;
                            currentLoop=i;
                            break;
                        }
                    }
                    if(!encontrado){
                        for(i=0; i<CACHESIZE; i++){
                            if(!loops[i].vectorizable){
                                encontrado=1;
                                currentLoop=i;
                                break;
                            }
                        }
                        if(!encontrado){
                            currentLoop = (currentLoop+1) % CACHESIZE;
                        }
                    }
                }
                
                
                LoopAnalysis.enable = 1;
                LoopAnalysis.iterationTimeSimd = 0;
                
                loops[currentLoop].firstAddress = instAddress;
                loops[currentLoop].lastAddress = prevInstAddress;
                loops[currentLoop].sequentialExecTime = when;
                loops[currentLoop].detectionLatency = when;
                loops[currentLoop].executions = 0;
                loops[currentLoop].iterations = 1;
                loops[currentLoop].predictedSize = 0;
                loops[currentLoop].definedSize = 0;
                loops[currentLoop].analyzed = 0;
                loops[currentLoop].discarded = 0;
                loops[currentLoop].vectorizable = 1;
                loops[currentLoop].storeInstAddress = 0;
                loops[currentLoop].storeDataAddress = 0;
                loops[currentLoop].storeDataSize = 0;
                loops[currentLoop].storeRegister = -1;
                
                DPRINTF(SIMDFLAG, "LOOP CACHE MISS\n");
                DPRINTF(SIMDFLAG, "Endereco inicial: %#x\n", instAddress);
                DPRINTF(SIMDFLAG, "Endereco final: %#x\n", prevInstAddress);
                DPRINTF(SIMDFLAG, "currentLoop: %d\n", currentLoop);
            }
        }
        //Branch not taken (termino do loop)
        else if((instAddress - prevInstAddress) == 4 && prevInstAddress == loops[currentLoop].lastAddress){
            loops[currentLoop].iterations++;
            loops[currentLoop].executions++;
            
            DPRINTF(SIMDFLAG, "LOOP FINALIZADO!  nº %d (%#x)\n", currentLoop, loops[currentLoop].lastAddress);
            DPRINTF(SIMDFLAG, "Tamanho previsto: %d\n", loops[currentLoop].predictedSize);
            DPRINTF(SIMDFLAG, "Tamanho de fato: %d\n", loops[currentLoop].iterations);
            
            if(loops[currentLoop].predictedSize != loops[currentLoop].iterations){
                loops[currentLoop].definedSize = 0;
            }
            if(!loops[currentLoop].definedSize){
                detectionLatency += 20000 * (loops[currentLoop].iterations-3);
            }
            
            //Registra ganho SIMD
            if(loops[currentLoop].vectorizable && loops[currentLoop].analyzed){
                int parallelism = (16 / loops[currentLoop].storeDataSize);
                int iterationsSisd = (loops[currentLoop].predictedSize - 3);
                int iterationsSimd = (iterationsSisd / parallelism);
                
                if((iterationsSisd % parallelism) != 0)
                    iterationsSimd++;
                
                long long int sequentialExecTime = when - loops[currentLoop].sequentialExecTime;
                long long int parallelExecTime = (loops[currentLoop].iterationTimeSimd * iterationsSimd);
                                
                if(loops[currentLoop].definedSize){
                    loop_def++;
                    
                    //totalticksvetorizados += sequentialExecTime - parallelExecTime - 70000;
                    totalticksvetorizados += sequentialExecTime - parallelExecTime;
                    DPRINTF(SIMDFLAG, "Ticks economizados: %lli\n", sequentialExecTime - parallelExecTime - 70000);
                    
                    ticks_parallel += parallelExecTime;
                    ticks_sequential += sequentialExecTime;
                    
                    
                    DPRINTF(STATFLAG, "ticks_sequential += %lli\n", sequentialExecTime);
                    DPRINTF(STATFLAG, "ticks_parallel   += %lli\n", parallelExecTime);
                    DPRINTF(STATFLAG, "ticks_sequential  = %lli\n", ticks_sequential);
                    DPRINTF(STATFLAG, "ticks_parallel    = %lli\n\n", ticks_parallel);
                }
                else{
                    loop_indef++;
                    
                    ticks_sequential_indef += sequentialExecTime;
                    
                    DPRINTF(STATFLAG, "ticks_sequential_indef += %lli\n", sequentialExecTime);
                    
                    if(loops[currentLoop].executions > 1){
                        //totalticksvetorizados_indef += sequentialExecTime - parallelExecTime - 70000;
                        totalticksvetorizados_indef += sequentialExecTime - parallelExecTime;
                        DPRINTF(SIMDFLAG, "Ticks economizados (indefinido): %lli\n", sequentialExecTime - parallelExecTime - 70000);
                        
                        ticks_parallel_indef += parallelExecTime;
                        
                        DPRINTF(STATFLAG, "ticks_parallel_indef   += %lli\n", parallelExecTime);
                        
                        //Calculo do desperdicio de ticks por erro de previsao
                        if(loops[currentLoop].iterations > loops[currentLoop].predictedSize){
                            int neededIterations = loops[currentLoop].iterations - loops[currentLoop].predictedSize;
                            long long int neededExecution = (sequentialExecTime / loops[currentLoop].iterations) * neededIterations;
                            
                            totalticksvetorizados_indef -= neededExecution;
                            
                            DPRINTF(SIMDFLAG, "Ticks desperdicados (indefinido): %lli\n", neededExecution);
                            
                            ticks_parallel_indef += neededExecution;
                        }
                        
                        DPRINTF(STATFLAG, "ticks_sequential_indef  = %lli\n", ticks_sequential_indef);
                        DPRINTF(STATFLAG, "ticks_parallel_indef    = %lli\n\n", ticks_parallel_indef);
                    }
                    
                    //Preve o numero de iteracoes da proxima execucao
                    loops[currentLoop].predictedSize = loops[currentLoop].iterations;
                }
                
                executaILP = 0;
            }
            
            loops[currentLoop].iterations = 0;
        }
    }
    
    else if(LoopAnalysis.enable && !(((instAddress-prevInstAddress)==4) || (instAddress == prevInstAddress))){
        loops[currentLoop].discarded = 1;
        loops[currentLoop].analyzed = 1;
        loops[currentLoop].vectorizable = 0;
        LoopAnalysis.enable = 0;
        
        DPRINTF(SIMDFLAG, "Descartando loop %d (descontinuo)\n", currentLoop);
    }
    
    
    //Registra a ocorrencia de possivel loop
    if(instruction[0]=='b'){
        if(instCond){
            possibleLoop = 1; //F[f].branch=1;
            
            if(LoopAnalysis.enable && instAddress != loops[currentLoop].lastAddress){
                loops[currentLoop].discarded = 1;
                loops[currentLoop].analyzed = 1;
                loops[currentLoop].vectorizable = 0;
                LoopAnalysis.enable = 0;
                
                DPRINTF(SIMDFLAG, "Descartando loop %d (cond)\n", currentLoop);
            }
        }
        
        if(LoopAnalysis.enable && instBranchSubRoutine){
            loops[currentLoop].discarded = 1;
            loops[currentLoop].analyzed = 1;
            loops[currentLoop].vectorizable = 0;
            LoopAnalysis.enable = 0;
            
            DPRINTF(SIMDFLAG, "Descartando loop %d (subrotina)\n", currentLoop);
        }
        
    }
    
    
    
    //Salva dados usados na comparacaoloop
    if(instCmp){
        LoopAnalysis.cmpsAddress = instAddress;
        
        //Comparacao com constante
        if(thereIsConstant){
            LoopAnalysis.cmpsOp1 = regContent[InstRegs.rs1];
            LoopAnalysis.cmpsOp2 = constante;
        }
        //Comparacao com registrador
        else{
            if(regContent[InstRegs.rs1] < regContent[InstRegs.rs2]){
                LoopAnalysis.cmpsOp1 = regContent[InstRegs.rs1];
                LoopAnalysis.cmpsOp2 = regContent[InstRegs.rs2];
            }
            else{
                LoopAnalysis.cmpsOp1 = regContent[InstRegs.rs2];
                LoopAnalysis.cmpsOp2 = regContent[InstRegs.rs1];
            }
        }
    }
    //Descarta dados apos sobrescricao
    else if(instSetFlag){
        LoopAnalysis.cmpsAddress = 0;
    }
    
    
    //Etapas de analise do loop
    if(LoopAnalysis.enable){
        //Verifica se um registrador com conteudo de store foi sobreescrito
        if(loops[currentLoop].storeDataAddress!=0){
            if(loops[currentLoop].storeRegister != -1 && (loops[currentLoop].storeRegister == InstRegs.rd1 || 
                                                          loops[currentLoop].storeRegister == InstRegs.rd2)){
                
                DPRINTF(SIMDFLAG, "Registrador com conteudo de store sobreescrito (r%d)\n", loops[currentLoop].storeRegister);
                
                loops[currentLoop].storeRegister = -1;
            }
        }
        if(loops[currentLoop].iterations == 1){
            //Armazenamento dos enderecos de dados dos stores
            if(loops[currentLoop].storeDataAddress==0){                
                if((instType=="MemWrite" && !instCond) && InstRegs.rs1 != -1 && InstRegs.rs2 != -1){
                    loops[currentLoop].storeInstAddress = instAddress;
                    loops[currentLoop].storeDataAddress = dataAddress;
                    
                    DPRINTF(SIMDFLAG, "Endereco armazenado: %#x\n", loops[currentLoop].storeDataAddress);
                    
                    // ANALISE DE REGISTRADOR
                    if(instMicro)
                        loops[currentLoop].storeRegister = InstRegs.rs1;
                    else
                        loops[currentLoop].storeRegister = InstRegs.rs2;
                    
                    DPRINTF(SIMDFLAG, "Registrador armazenado: %d\n", loops[currentLoop].storeRegister);
                }
            }
            
            /*
            //Analise de latencia do loop
            bool dataDependency=0;
            int instSimdLatency=0;
            
            //Analise de dependencia de dados entre instrucoes
            if((((PrevRegs.rd1 == InstRegs.rs1 || PrevRegs.rd1 == InstRegs.rs2) ||
                 (PrevRegs.rd1 == InstRegs.rs3 || PrevRegs.rd1 == InstRegs.rs4)) && PrevRegs.rd1 != -1) ||
               (((PrevRegs.rd2 == InstRegs.rs1 || PrevRegs.rd2 == InstRegs.rs2) ||
                 (PrevRegs.rd2 == InstRegs.rs3 || PrevRegs.rd2 == InstRegs.rs4)) && PrevRegs.rd2 != -1))
                dataDependency=1;
            
            //Caso haja dependencia de dados entre instrucoes de mesmo tipo ha latencia de espera por unidades funcionais
            //Instrucoes de divisao ou raiz quadrada nao sao pipelinezaveis tambem tem latencia de espera
            if((dataDependency && prevInstType==instType) || instType=="IntDiv" || instType=="FloatDiv" || instType=="FloatSqrt"){
            */
            
            if(!instMicro){
                int instSimdLatency=0;
                
                //Instrucoes de divisao ou raiz quadrada nao sao pipelinezaveis tambem tem latencia de espera
                if(instType=="IntDiv" || instType=="FloatDiv" || instType=="FloatSqrt"){
                    for(i=0; i<12; i++){
                        if(instType==InstLatency[i].instType){
                            instSimdLatency = 10000 * InstLatency[i].simdLatency;
                            break;
                        }
                    }
                }
                else
                    instSimdLatency = 10000;
                
                
                LoopAnalysis.iterationTimeSimd += instSimdLatency;
            }
        }
        else if(loops[currentLoop].iterations == 2){
            //Verifica load de dado em endereco salvo na primeira iteracao
            if(instType=="MemRead" && !instCond){
                if(dataAddress == loops[currentLoop].storeDataAddress){
                    loops[currentLoop].vectorizable = 0;
                    
                    DPRINTF(SIMDFLAG, "Load de dado em endereco salvo na primeira iteracao\n");
                }
            }
            //Verifica se um registrador com conteudo de store foi reutilizado
            if(!instCmp && loops[currentLoop].storeRegister >= 0 &&
                          (loops[currentLoop].storeRegister == InstRegs.rs1 ||
                           loops[currentLoop].storeRegister == InstRegs.rs2 ||
                           loops[currentLoop].storeRegister == InstRegs.rs3 ||
                           loops[currentLoop].storeRegister == InstRegs.rs4)){
                loops[currentLoop].vectorizable = 0;
                
                DPRINTF(SIMDFLAG, "Registrador com conteudo de store reutilizado\n");
            }
            
            //Armazena o tamanho do dado salvo em bytes
            if((instType=="MemWrite" && !instCond) && instAddress == loops[currentLoop].storeInstAddress){
                loops[currentLoop].storeDataSize = dataAddress - loops[currentLoop].storeDataAddress;

                DPRINTF(SIMDFLAG, "Tamanho do dado em bytes %d\n", loops[currentLoop].storeDataSize);
            }
        }
    }
    
    
    
    prevInst=instruction;
    prevInstType = instType;
    prevInstAddress = instAddress;
    
    PrevRegs = InstRegs;
}



void Trace::ExeTracerRecord::dump()
{
    if (Debug::ExecMacro && staticInst->isMicroop() &&
        ((Debug::ExecMicro &&
            macroStaticInst && staticInst->isFirstMicroop()) ||
            (!Debug::ExecMicro &&
             macroStaticInst && staticInst->isLastMicroop()))) {
        traceInst(macroStaticInst, false);
    }
    if (Debug::ExecMicro || !staticInst->isMicroop()) {
        traceInst(staticInst, true);
    }
}

} // namespace Trace

Trace::ExeTracer *
ExeTracerParams::create()
{
    return new Trace::ExeTracer(this);
}

