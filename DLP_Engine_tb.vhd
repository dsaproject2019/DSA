library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use STD.textio.all;
use ieee.std_logic_textio.all;       

entity DLP_Engine_tb is
end DLP_Engine_tb;
 
architecture behavioral of DLP_Engine_tb is
    
      signal clk : std_logic := '0';  
      signal rst: std_logic;
      signal pc_atual : std_logic_vector(31 downto 0);
      signal inst : std_logic_vector(3 downto 0);
      signal address_data : std_logic_vector(31 downto 0);
      signal rsrc  : std_logic_vector(4 downto 0);
      signal rdst  : std_logic_vector(4 downto 0);

      signal data : std_logic_vector(31 downto 0);
      signal data2 : std_logic_vector(31 downto 0); 
       
      file     mem_inst:       text; 
    
begin
    
    DLP_ENGINE: entity work.DLP_Engine 
        port map (
            pc_atual => pc_atual,
            inst => inst,
            address_data => address_data,
            rsrc => rsrc,
            rdst => rdst,
            data => data,
            data2 => data2,
            clk => clk, 
            rst => rst            
        );
       
    -- Generates the clock signal            
    clk <= not clk after 15 ns;
    
    -- Generates the reset signal
    rst <='1', '0' after 1 ns;
  
    process (clk)
      variable mem_line:       line;
      variable v_SPACE     : character;
      variable line_counter:   integer := 0;
      variable target_line:    integer := 1;
      
      variable v_pc_atual : std_logic_vector(31 downto 0);
      variable v_inst : std_logic_vector(3 downto 0);
      variable v_data : std_logic_vector(31 downto 0);
      variable v_address_data : std_logic_vector(31 downto 0);
      variable v_data2 : std_logic_vector(31 downto 0);
      variable v_rsrc  : std_logic_vector(4 downto 0);        
      variable v_rdst  : std_logic_vector(4 downto 0);     
       
      
      begin
        
          if rst = '1' then
            pc_atual <= "00000000000000000000000000000000";
            inst <= "0000";
            address_data <= "00000000000000000000000000000000";
            rsrc <= "00000";
            rdst <= "00000"; 
            data <= "00000000000000000000000000000000";
            data2 <= "00000000000000000000000000000000";                                                            
            
          elsif clk'event and clk = '1' then
                  
                  file_open(mem_inst, "/home/tiago/Desktop/UFSM/DSA/src/input_vectors.txt", read_mode); 
                  
                  while line_counter < target_line loop
                    if not endfile(mem_inst) then 
                      readline(mem_inst, mem_line);
                      read(mem_line, v_pc_atual);
                      read(mem_line, v_SPACE);           
                      read(mem_line, v_inst);
                      read(mem_line, v_SPACE);           
                      read(mem_line, v_data);
                      read(mem_line, v_SPACE);           
                      read(mem_line, v_data2);
                      read(mem_line, v_SPACE);           
                      read(mem_line, v_rsrc);
                      read(mem_line, v_SPACE);           
                      read(mem_line, v_rdst);
                      read(mem_line, v_SPACE);           
                      read(mem_line, v_address_data);
                    end if;
                    line_counter := line_counter + 1;
                  end loop;     
                  file_close(mem_inst);
                  
                  target_line := target_line + 1;
                  line_counter := 0;
                  
                  pc_atual <= v_pc_atual;
                  inst <= v_inst;
                  address_data <= v_address_data;
                  rsrc <= v_rsrc;
                  rdst <= v_rdst;                  
                  data <= v_data;
                  data2 <= v_data2; 
          else
            
          end if;           

    end process;
      
end behavioral;
