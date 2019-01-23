library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_unsigned.all;

entity DLP_Engine is
port(	

    enable_DLP_Engine : out std_logic;   
    
    
    pc_atual : in std_logic_vector(31 downto 0);
    inst : in std_logic_vector(3 downto 0);
    data : in std_logic_vector(31 downto 0);
    address_data : in std_logic_vector(31 downto 0);
    data2 : in std_logic_vector(31 downto 0); 
    rsrc  : in std_logic_vector(4 downto 0);       
    rdst  : in std_logic_vector(4 downto 0);    

    clk : in std_logic;
    rst : in std_logic
);

end DLP_Engine;

--------------------------------------------------------

architecture behavioral of DLP_Engine is

     
    type ipMemType is array (0 to 3) of std_logic_vector(18 downto 0);
    type addrMemType is array (0 to 4) of std_logic_vector(12 downto 0);
    signal execute_DLP_Engine : std_logic;
    
    -- Estados originais
    --TYPE State_type IS (LOOP_DETECTION, DATA_COLLECTION, DEPENDENCY_ANALYSIS, STORE_ID_EXECUTION, EXECUTION, HALT); 
    
    -- Estados atuais
    TYPE State_type IS (LOOP_DETECTION, DATA_COLLECTION, DEPENDENCY_ANALYSIS, STORE_ID_EXECUTION, MAPPING, EXECUTION, HALT);
    
    -- Estados finais
    --TYPE State_type IS (LOOP_DETECTION, DATA_COLLECTION, DEPENDENCY_ANALYSIS, STORE_ID_EXECUTION, MAPPING, SPECULATIVE_EXECUTION, EXECUTION, HALT);
    
    SIGNAL state : State_type;
 
begin

    enable_DLP_Engine <= execute_DLP_Engine;

    process (clk, rst)
        -- Variaveis de leitura de arquivo
        
        variable v_pc_anterior : std_logic_vector(7 downto 0);
        variable v_data_add : std_logic_vector(7 downto 0);
        variable v_rdst_add  : std_logic_vector(4 downto 0);
        variable v_id_afterbranch : std_logic_vector(7 downto 0);

        variable v_DLP_Engine : integer := 0;        
        variable verify_size : integer := 0;     
        variable loop_size : std_logic_vector(7 downto 0) := "00000000";
        variable temp_size_logic : std_logic_vector(7 downto 0) := "00000000";
        variable hit_cache: integer := 0;
        variable previous_was_branch: integer := 0;
        variable previous_was_add: integer := 0;

        
        --DEFININDO O LOOP
        variable undefined_loop: integer := 0;
        variable undefined_sized_loop: integer := 0;
        variable count_loop: integer := 0;
        variable id_verify: std_logic_vector(18 downto 0);
        --DEFININDO O LOOP
        
        variable memory_gap: integer := 0;
        variable size_multiplier: integer :=0;
        variable module_address: integer := 0;
        variable preempt_address: integer := 0;
        
        variable DSA_cache : ipMemType := (others => "1111111111111111111");
        variable Verification_cache : addrMemType := (others => "1111111111111");
        
        
        -- Variaveis Tiago
        variable v_cond_branch_add : std_logic_vector(7 downto 0) := (others => '1');
        variable v_executed_inst :  std_logic_vector(32 downto 0) := (others => '0');
        
        
    begin       
            
        if rst = '1' then
            state <= LOOP_DETECTION;
            
        elsif clk'event and clk = '1' then
                    
            case state is
                
                when LOOP_DETECTION =>
                
                    Verification_cache := (others => "1111111111111");
                    loop_size := "00000000";
                    verify_size := 0;
                    temp_size_logic := "00000000";
                    hit_cache := 0;
                             
                    -- Caso a ultima instrucao tenha sido um branch e o PC regrediu durante a execucao normal, verifica se nao ha uma configuracao existente a ser executada na DLP Engine                 
                    if (pc_atual(7 downto 0) < v_pc_anterior) and (previous_was_branch = 1) and v_DLP_Engine = 0 then

                        --s_busca_mem <= '1';
                        v_id_afterbranch := pc_atual(7 downto 0); 
                        -- Caso exista uma configuracao, o DLP Engine e ativado                     
                        for i in 0 to 3 loop
                            if DSA_cache(i)(7 downto 0) = v_id_afterbranch(7 downto 0) then
                              
                                hit_cache := 1;
                                v_DLP_Engine := 1;                          

                                if DSA_cache(i)(18 downto 16) = "000" then
                                    undefined_loop := 1;
                                    count_loop := 0;
                                    undefined_sized_loop := 1;
                                    id_verify := DSA_cache(i);
                                elsif DSA_cache(i)(18 downto 16) = "001" then
                                    count_loop := 1;
                                    undefined_sized_loop := 0;
                                    undefined_loop := 0;
                                elsif DSA_cache(i)(18 downto 16) = "111" then
                                    undefined_sized_loop := 1;
                                    undefined_loop := 0;
                                    count_loop := 0;
                                end if;
                                
                                exit;
                            else
                               execute_DLP_Engine <= '0';
                            end if; 
                        end loop;
                        
                        -- Caso nao exista uma configuracao, o estado de analise de loop e ativado
                        if hit_cache = 0 then
                            --s_loop_analysis <= '1';
                            execute_DLP_Engine <= '0';

                            -- Caso tenha ocorrido uma instrucao do tipo store, salva o endereco de acesso para verificacao de vetorizacao
                          
                            if inst = "1010" then 
                                --s_st_mem <= '1';
                                --s_access_addrrmemory <= '1';
                                for i in 0 to 4 loop
                                    if Verification_cache(i) = "1111111111111" then
                                        Verification_cache(i)(7 downto 0) := address_data(7 downto 0);
                                        Verification_cache(i)(8) := '0';
                                        Verification_cache(i)(12 downto 9) := pc_atual(3 downto 0);
                                        exit;
                                    end if; 
                                end loop; 
                            end if;
                            
                            state <= DATA_COLLECTION;
                          
                        else
                            previous_was_branch := 0;
                          
                            if count_loop = 1 then
                                count_loop := 0;
                                execute_DLP_Engine <= '1';
                                state <= EXECUTION;
                              
                            elsif undefined_loop = 1 or undefined_sized_loop = 1 then
                              
                                -- Caso tenha ocorrido uma instrucao do tipo add  
                                if inst = "0010" then
                                    v_rdst_add := rdst;
                                    v_data_add := data(7 downto 0);
                                    previous_was_add := 1; 
                                    previous_was_branch := 0;                  

                                elsif inst = "1010" then 
                              
                                    for i in 0 to 4 loop
                                        if Verification_cache(i) = "1111111111111" then
                                            Verification_cache(i)(7 downto 0) := address_data(7 downto 0);
                                            Verification_cache(i)(8) := '0';
                                            Verification_cache(i)(12 downto 9) := pc_atual(3 downto 0);
                                            exit;
                                        end if; 
                                    end loop;          

                                elsif inst = "1011" then
                              
                                    for i in 0 to 4 loop
                                        if Verification_cache(i) = "1111111111111" then
                                            Verification_cache(i)(7 downto 0) := address_data(7 downto 0);
                                            Verification_cache(i)(8) := '1';
                                            Verification_cache(i)(12 downto 9) := pc_atual(3 downto 0);
                                            exit;
                                        end if; 
                                    end loop;                             
                            end if;
                             
                            state <= DATA_COLLECTION; 
                             
                        end if;
                    end if;
                    
                    else
                        execute_DLP_Engine <= '0';
                        --s_busca_mem <= '0';
                        state <= LOOP_DETECTION;    
                    end if;
                                   
                    -- Verifica se a instrucao atual e um branch e entao seta a flag previous_was_branch
                    if inst = "0000" then                                  
                        previous_was_branch := 1;
                        state <= LOOP_DETECTION;                                   
                    end if;                              

                    if inst = "1111" then
                        state <= HALT;
                    end if;
                    
                    -- Armazena pc anterior para logica de loop     
                    v_pc_anterior := pc_atual(7 downto 0);              
      
                
                -------------------------------------------------------------------------------------------------------------------------------
                  
                when DATA_COLLECTION =>
        
                
                    -- Fim da logica de leitura de instrucoes de entrada
                  
                    -- Comeco da analise de loop
                    execute_DLP_Engine <= '0';

                    -- Caso alguma instrucao do tipo add tenha ocorrido e apos (nao necessariamente em sequencia) uma instrucao cmps tenha ocorrido, a verificacao do tamanho do loop pode ser feita
                    if inst = "0001" and previous_was_add = 1 then
                        previous_was_add := 0;
                    
                        -- PREVISAO DO TAMANHO DO LOOP
                    
                        for i in 0 to 3 loop  
                            -- Caso o registrador destino do add coincida com o src do cmps                    
                            if v_rdst_add(i) = rsrc(i) then
                            
                                -- Caso o dado presente no registrador src1 de cmps seja maior do que o registrador src2  
                                if data > data2 then
                                -- loop_size = (v_data - v_data2)/incremento 
                                                        
                                    for i in 0 to 128 loop
                                        if temp_size_logic > (data(7 downto 0) - data2(7 downto 0)) then
                                            exit;
                                        end if;
                                        
                                        loop_size := loop_size + 1;
                                        temp_size_logic := v_data_add + temp_size_logic;
                                        
                                    end loop;
                                 
                                --s_size <= loop_size;
                                
                                -- Caso o dado presente no registrador src2 de cmps seja maior do que o registrador src1                                  
                                elsif data < data2 then
                                    -- loop_size = (v_data2 - v_data1)/incremento 
                                    for i in 0 to 128 loop
                                        if temp_size_logic > (data2(7 downto 0) - data(7 downto 0)) then
                                            exit;
                                        end if;
                                        
                                        loop_size := loop_size + 1;
                                        temp_size_logic := v_data_add + temp_size_logic;      
                                                                  
                                    end loop;
                                    
                                --s_size <= loop_size;
                                end if; 
                            
                            -- Tamanho do loop ja verificado                         
                            verify_size := 1;                                            
                            end if;                    
                        end loop;
                    
                        if undefined_loop = 1 and verify_size = 1 then
                            undefined_loop := 0;
                            if loop_size /= id_verify(15 downto 8) then

                                for i in 0 to 3 loop
                                    if DSA_cache(i)(7 downto 0) = id_verify(7 downto 0) then
                                        DSA_cache(i)(18 downto 16) := "111";  
                                    end if;
                                end loop; 
                                
                                undefined_sized_loop := 1;
                                state <= DATA_COLLECTION;    
     
                            elsif loop_size = id_verify(15 downto 8) then
                              
                                for i in 0 to 3 loop
                                    if DSA_cache(i)(7 downto 0) = id_verify(7 downto 0) then
                                        DSA_cache(i)(18 downto 16) := "001";  
                                    end if;
                                end loop;
                                
                                state <= EXECUTION;
                                
                            end if;
                        end if;
                    
                    
                    -- Caso tenha ocorrido uma instrucao do tipo add  
                    elsif inst = "0010" then
                        v_rdst_add := rdst;
                        v_data_add := data(7 downto 0);
                        previous_was_add := 1; 
                        previous_was_branch := 0;
                        
                        state <= DATA_COLLECTION;
                  
                    -- Caso tenha ocorrido uma instrucao do tipo branch 
                    elsif inst = "0000" then 
                        previous_was_branch := 1;
                        
                        
                        -- Implementacao atual
                        
                        if (v_id_afterbranch /= pc_atual(7 downto 0)) then
                            
                            if (v_cond_branch_add = "11111111") then
                                state <= DEPENDENCY_ANALYSIS;
                            else
                                state <= MAPPING;
                            end if;
                        
                        else
                            v_cond_branch_add := pc_atual(7 downto 0);
                        
                        end if;
                    
                    -- Caso tenha ocorrido uma instrucao do tipo store, salva o endereco de acesso para verificacao de vetorizacao
                    elsif inst = "1010" then 

                        for i in 0 to 4 loop
                            if Verification_cache(i) = "1111111111111" then
                                Verification_cache(i)(7 downto 0) := address_data(7 downto 0);
                                Verification_cache(i)(8) := '0';
                                Verification_cache(i)(12 downto 9) := pc_atual(3 downto 0);
                                exit;
                            end if; 
                        end loop; 
                                      
                        state <= DATA_COLLECTION;

                    elsif inst = "1011" then
 
                        for i in 0 to 4 loop
                            if Verification_cache(i) = "1111111111111" then
                                Verification_cache(i)(7 downto 0) := address_data(7 downto 0);
                                Verification_cache(i)(8) := '1';
                                Verification_cache(i)(12 downto 9) := pc_atual(3 downto 0);
                                exit;
                            end if; 
                        end loop;
                        
                        state <= DATA_COLLECTION;
                    
                    else
                        state <= DATA_COLLECTION;
                    end if;
                                   
                    if inst = "1111" then
                        state <= HALT;
                    end if;
            
                  
                -------------------------------------------------------------------------------------------------------------------------------                                  
                
                when DEPENDENCY_ANALYSIS =>
                  

                    execute_DLP_Engine <= '0';                                                      

                    -- Caso o ID seja igual ao PC atual, e a instrucao anterior representou um salto, o proximo estado de verificacao de loop e ativado
                    if (v_id_afterbranch = pc_atual(7 downto 0)) and previous_was_branch = 1 then 
                        previous_was_branch := 0;
                        state <= DEPENDENCY_ANALYSIS;                      
                    -- Caso o ID nao seja igual ao PC atual, e a instrucao anterior representou um salto, a verificacao de loop e desativada   
                    elsif (v_id_afterbranch /= pc_atual(7 downto 0)) and previous_was_branch = 1 then                      
                        previous_was_branch := 0;                    
                        state <= LOOP_DETECTION;                    
                    else 
                        state <= DEPENDENCY_ANALYSIS;                      
                    end if;

                    -- Verifica se e uma instrucao do tipo LOAD, caso seja e esteja acessando um endereco atrelado a etapa anterior do loop
                    -- o loop nao pode ser vetorizado                  

                    if inst = "1011" then

                        for i in 0 to 4 loop
                            if Verification_cache(i)(7 downto 0) = address_data(7 downto 0) and Verification_cache(i)(8) = '0' then
                                state <= LOOP_DETECTION;
                                exit;
                                
                            -- PREEMPCAO DE DEPENDENCIA PARA TODOS ENDERECOS CARREGADOS    
                            elsif Verification_cache(i)(8) = '1' and Verification_cache(i)(12 downto 9) = pc_atual(3 downto 0) and Verification_cache(i) /= "1111111111111" then 

                                memory_gap :=  to_integer(unsigned(address_data(7 downto 0))) - to_integer(unsigned(Verification_cache(i)(7 downto 0)));               
                               
                                for j in 0 to 4 loop
                                    if Verification_cache(j)(8) = '0' then
                                        size_multiplier := to_integer(unsigned(loop_size)) - 3;
                                        preempt_address := to_integer(unsigned(Verification_cache(i)(7 downto 0))) + memory_gap*size_multiplier;

                                        if preempt_address < to_integer(unsigned(Verification_cache(j)(7 downto 0))) then
                                            exit;                                    
                                        elsif preempt_address > to_integer(unsigned(Verification_cache(j)(7 downto 0))) then     
                                            module_address := to_integer(unsigned(Verification_cache(j)(7 downto 0))) mod memory_gap;
                                            
                                            if module_address = 0 then
                                                state <= LOOP_DETECTION;
                                            end if;
                                            
                                            exit;
                                        end if;
                                    end if;
                                end loop;
                        --                           memory_gap := address_data - Verification_cache(i)(31 downto 0);               
                        --                           
                        --                           for j in 0 to 9 loop
                        --                             if Verification_cache(j)(32) = '0' then
                        --                                 preempt_address := Verification_cache(i)(31 downto 0);
                        --                                 for z in 0 to 64 loop
                        --                                     if z > loop_size then
                        --                                         exit;
                        --                                     end if;
                        --                                     if preempt_address = Verification_cache(j)(31 downto 0) then
                        --                                       state <= LOOP_DETECTION;
                        --                                       exit;                                    
                        --                                     end if;
                        --                                     preempt_address := preempt_address + memory_gap;
                        --                                 end loop; 
                        --                             end if;
                        --                           end loop;
                               
                            end if; 
                            --preempt_address := "00000000000000000000000000000000";
                            memory_gap := 0;
                            module_address := 0;
                            preempt_address := 0;
                        end loop;
                    end if;

                    -- Caso a instrucao atual seja um branch
                    if inst = "0000" then 
                        previous_was_branch := 1;                  
                        state <= STORE_ID_EXECUTION;
                    end if;   

                    if inst = "1111" then
                        state <= HALT;
                    end if;
                
                -------------------------------------------------------------------------------------------------------------------------------                                  
                                  
                when STORE_ID_EXECUTION =>
                  
                    --s_loop_analysis <= '1';
                    --s_access_addrmemory <= '0';
                    --s_ver_ld <= '0';
                    --s_st_mem <= '0';
                    --s_busca_mem <= '0';
                                    

                    -- Caso o ID seja igual ao PC atual, e a instrucao anterior representou um salto, o loop e vetorizavel                  
                    if (v_id_afterbranch = pc_atual(7 downto 0)) and previous_was_branch = 1 and undefined_sized_loop = 0  then 
                     
                        -- Caso seja um loop vetorizavel, o ID deste loop pode ser salvo a memoria de DLP_Engine
                        for i in 0 to 3 loop
                            if DSA_cache(i) = "1111111111111111111" then
                                DSA_cache(i)(7 downto 0) := v_id_afterbranch(7 downto 0);
                                DSA_cache(i)(15 downto 8) := loop_size;
                                DSA_cache(i)(18 downto 16) := "000";
                                exit;
                            end if; 
                        end loop;

                        previous_was_branch := 0;
                        execute_DLP_Engine <= '1'; 
                        v_DLP_Engine := 1;
                        
                        for i in 0 to 4 loop
                            Verification_cache(i) := "1111111111111"; 
                        end loop; 

                        state <= EXECUTION;
                     
                    -- Caso o ID nao seja igual ao PC atual, e a instrucao anterior representou um salto, o loop chegou ao fim 
                    elsif (v_id_afterbranch = pc_atual(7 downto 0)) and previous_was_branch = 1 and undefined_sized_loop = 1  then

                        previous_was_branch := 0;
                        execute_DLP_Engine <= '1'; 
                        v_DLP_Engine := 1;
                        
                        for i in 0 to 4 loop
                            Verification_cache(i) := "1111111111111"; 
                        end loop;
                        
                        state <= EXECUTION; 
                    
                    elsif (v_id_afterbranch /= pc_atual(7 downto 0)) and previous_was_branch = 1 then                      
                        previous_was_branch := 0; 
                        execute_DLP_Engine <= '0';                   
                        state <= LOOP_DETECTION;
                    else
                        execute_DLP_Engine <= '0';
                        state <= STORE_ID_EXECUTION;
                    end if;

                    if inst = "1111" then
                        state <= HALT;
                    end if;
                
                
                -- Implementacao atual
                
                when MAPPING =>
                    
                    -- Caso haja um branch 
                    if (previous_was_branch = 1) then
                        
                        previous_was_branch := 0;
                        
                        -- Caso o branch esteja dentro do range do loop (condicao)
                        --if v_id_afterbranch /= pc_atual(7 downto 0) then
                    end if;

                  
                when EXECUTION =>
                     
                    undefined_sized_loop := 0;
                    undefined_loop := 0;
                    count_loop := 0;
                    
                    -- Caso a ultima instrucao tenha sido um branch durante a execucao da DLP Engine, caso o id_afterbranch nao seja o mesmo, este e o fim da execucao em DLP Engine                  
                    if (previous_was_branch = 1) and v_DLP_Engine = 1 then
                    
                        previous_was_branch := 0;
                        
                        if v_id_afterbranch /= pc_atual(7 downto 0) then
                            execute_DLP_Engine <= '0';
                            v_DLP_Engine := 0;
                            state <= LOOP_DETECTION;
                        else
                            execute_DLP_Engine <= '1'; 
                            v_DLP_Engine := 1;                   
                        end if;
                    else
                        execute_DLP_Engine <= '1';
                        v_DLP_Engine := 1;
                        state <= EXECUTION;
                    end if;

                    -- Verifica se a instrucao atual e um branch e entao seta a flag previous_was_branch
                    if inst = "0000" then   
                        execute_DLP_Engine <= '1';
                        v_DLP_Engine := 1;             
                        previous_was_branch := 1;
                        state <= EXECUTION;
                    end if; 

                    if inst = "1111" then
                        state <= HALT;
                    end if;
                
                
                when HALT =>
                    execute_DLP_Engine <= '0'; 

               end case;  
        end if;
    end process;

end behavioral;

--------------------------------------------------------
