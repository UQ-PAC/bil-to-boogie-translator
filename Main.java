import Facts.DatalogUtility;
import Facts.Fact;
import Facts.inst.InstFact;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Main {
    public static void main(String[] args) throws IOException {
        if (args.length == 0) {
            System.out.println("usage: Main.java input_bil_file [datalog] [boogie]");
        }
        // generate abstract syntax tree
        BilLexer bilLexer = new BilLexer(CharStreams.fromFileName(args[0]));
        CommonTokenStream tokens = new CommonTokenStream(bilLexer);
        BilParser parser = new BilParser(tokens);
        parser.setBuildParseTree(true);
        BilParser.BilContext b = parser.bil(); // abstract syntax tree

        // extract all statement objects from the tree
        List<InstFact> facts = new ArrayList<>();
        StatementLoader statementLoader = new StatementLoader(facts);
        ParseTreeWalker walker = new ParseTreeWalker();
        walker.walk(statementLoader, b);

        List<String> argsList = Arrays.asList(args);

        if (argsList.contains("datalog")) {
            List<DatalogUtility.Log> logs = new DatalogUtility().createDatalog(facts);
            try {
                BufferedWriter instWriter = new BufferedWriter(new FileWriter("DatalogFacts/inst.facts"));
                BufferedWriter expWriter = new BufferedWriter(new FileWriter("DatalogFacts/exp.facts"));
                BufferedWriter succWriter = new BufferedWriter(new FileWriter("DatalogFacts/succ.facts"));
                for (DatalogUtility.Log log : logs) {
                    BufferedWriter writer = log instanceof DatalogUtility.InstLog ? instWriter :
                            log instanceof DatalogUtility.ExpLog ? expWriter : succWriter;
                    writer.write(log.toString());
                    writer.newLine();
                    writer.flush();
                }
            } catch (IOException e) {
                System.err.println("Error writing to datalog files.");
            }
        }

        if (argsList.contains("boogie")) {
            BoogieTranslator translator = new BoogieTranslator(facts, "boogie_out.txt");
            translator.translate();
        }

        /*

        ParseTreeWalker walker = new ParseTreeWalker();
        walker.walk(statementLoader, b);

        // analyse statements and convert to boogie
        BoogieTranslator translator = new BoogieTranslator(lines, "boogie_out.txt");
        translator.translate();*/

        /*
        // clean the output file from the listener and put the cleaned version in the file called finalBoogieCode
        String finalBoogieCode = "finalBoogie.txt";
        BoogieCleaner cleaner = new BoogieCleaner(outFile, finalBoogieCode);
        cleaner.clean();
        */
    }
}
