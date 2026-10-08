import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import org.omg.sysml.interactive.SysMLInteractive;

/** Local, headless validation using the pinned official pilot implementation. */
public final class Validate {
    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            System.err.println("Usage: agda2sysml-validate LIBRARY MODEL");
            System.exit(1);
        }
        var engine = SysMLInteractive.createInstance();
        engine.setVerbose(false);
        engine.loadLibrary(args[0]);
        var result = engine.process(Files.readString(Path.of(args[1]), StandardCharsets.UTF_8));
        if (result.getException() != null) {
            System.err.println(result.formatException());
            System.exit(1);
        }
        if (result.hasErrors() || result.hasWarnings()) {
            System.err.println(result.formatIssues());
        }
        if (result.hasErrors()) System.exit(1);
    }
}
