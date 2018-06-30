#include <iostream>

#include <fdr/fdr.h>

static void describe_behaviour(
    const FDR::Session& session,
    const FDR::Assertions::DebugContext& debug_context,
    const FDR::Assertions::Behaviour& behaviour,
    unsigned int indent,
    const bool recurse)
{

    std::cout << "behaviour_type:";
    indent += 2;
    if (dynamic_cast<const FDR::Assertions::ExplicitDivergenceBehaviour*>(&behaviour))
        std::cout << "explicit divergence after trace";
    else if (dynamic_cast<const FDR::Assertions::IrrelevantBehaviour*>(&behaviour))
        std::cout << "irrelevant";
    else if (auto loop =
            dynamic_cast<const FDR::Assertions::LoopBehaviour*>(&behaviour))
        std::cout << "loops after index" << loop->loop_index();
    else if (auto min_acceptance =
        dynamic_cast<const FDR::Assertions::MinAcceptanceBehaviour*>(&behaviour))
    {
        std::cout << "minimal acceptance refusing {";
        for (const FDR::LTS::CompiledEvent event : min_acceptance->min_acceptance())
            std::cout << session.uncompile_event(event)->to_string() << "*";
        std::cout << "}";
    }
    else if (auto segmented =
        dynamic_cast<const FDR::Assertions::SegmentedBehaviour*>(&behaviour))
    {
        std::cout << "Segmented behaviour consisting of:\n";

        for (const std::shared_ptr<FDR::Assertions::Behaviour>& child :
                segmented->prior_sections())
            describe_behaviour(session, debug_context, *child, indent + 2, false);
        describe_behaviour(session, debug_context, *segmented->last(),
            indent + 2, false);
    }
    else if (auto trace = dynamic_cast<const FDR::Assertions::TraceBehaviour*>(&behaviour))
        std::cout << "performs event " << session.uncompile_event(trace->error_event())->to_string();
    std::cout << std::endl;

    std::cout << std::string(indent, ' ') << "Trace:";
    for (const FDR::LTS::CompiledEvent event : behaviour.trace())
    {
        if ((event != FDR::LTS::INVALID_EVENT) && (event != FDR::LTS::TAU))
            std::cout << session.uncompile_event(event)->to_string() << "*";
    }
    std::cout << std::endl;

    std::cout << std::string(indent, ' ') << "End";
   
    std::cout << std::endl;

    if (recurse)
    {
        for (const std::shared_ptr<FDR::Assertions::Behaviour>& child :
                debug_context.behaviour_children(behaviour))
        {
		if(indent > 9)	{
		break;
		}	
		
            describe_behaviour(session, debug_context, *child, indent + 2, true);
        }
    }
}


static void describe_counterexample(
    const FDR::Session& session,
    const FDR::Assertions::Counterexample& counterexample)
{

    std::cout << "Counterexample_type:";
    if (dynamic_cast<const FDR::Assertions::DeadlockCounterexample*>(
            &counterexample))
        std::cout << "deadlock";
    else if (dynamic_cast<const FDR::Assertions::DeterminismCounterexample*>(
                &counterexample))
        std::cout << "determinism";
    else if (dynamic_cast<const FDR::Assertions::DivergenceCounterexample*>(
                &counterexample))
        std::cout << "divergence";
    else if (auto min_acceptance =
            dynamic_cast<const FDR::Assertions::MinAcceptanceCounterexample*>(
                &counterexample))
    {
        std::cout << "minimal acceptance refusing {";
        for (const FDR::LTS::CompiledEvent event : min_acceptance->min_acceptance())
            std::cout << session.uncompile_event(event)->to_string() << "*";
        std::cout << "}";
    }
    else if (auto trace =
            dynamic_cast<const FDR::Assertions::TraceCounterexample*>(
                &counterexample))
        std::cout << "trace with event " << session.uncompile_event(
            trace->error_event())->to_string();
    else
        std::cout << "unknown";
    std::cout << std::endl;

    if (auto refinement_counterexample =
            dynamic_cast<const FDR::Assertions::RefinementCounterexample*>(
                &counterexample))
    {
      
        FDR::Assertions::DebugContext debug_context(*refinement_counterexample,
            false);
        debug_context.initialise(nullptr);
        describe_behaviour(session, debug_context,
            *debug_context.root_behaviours()[0], 2, true);
        describe_behaviour(session, debug_context,
            *debug_context.root_behaviours()[1], 2, true);
	
    }
    else if (auto property_counterexample =
            dynamic_cast<const FDR::Assertions::PropertyCounterexample*>(
                &counterexample))
    {
       
        FDR::Assertions::DebugContext debug_context(*property_counterexample,
            false);
        debug_context.initialise(nullptr);
        describe_behaviour(session, debug_context,
            *debug_context.root_behaviours()[0], 2, true);
    }
}


static int main_function(int& argc, char**& argv)
{
    if (!FDR::has_valid_license())
    {
        std::cout << "Please run refines or FDR4 to obtain a valid license before running this." << std::endl;
        return EXIT_FAILURE;
    }
        
    std::cout << "Using " << FDR::version() << std::endl;

    if (argc != 2)
    {
        std::cerr << "Expected exactly one argument." << std::endl;
        return EXIT_FAILURE;
    }

    const std::string file_name = argv[1];

    std::cout << "Loading " << file_name << std::endl;

    FDR::Session session;

   
    try
    {
        session.load_file(file_name);
    }
    catch (const FDR::FileLoadError& error)
    {
        std::cout << "Could not load. Error: " << error.what() << std::endl;
        return EXIT_FAILURE;
    }


    for (const std::shared_ptr<FDR::Assertions::Assertion>& assertion
            : session.assertions())
    {
        std::cout << "Checking:" << assertion->to_string() << std::endl;

        try
        {
            assertion->execute(nullptr);
            std::cout << "Result:";
 	    std::cout
                << (assertion->passed() ? "Passed" : "Failed")
                << ", found " << assertion->counterexamples().size()
                << " counterexamples" << std::endl;

	        //std::cout << assertion.BFSRefinementProgress() << std::endl;
		//const std::shared_ptr <FDR::Assertions::BFSRefinementProgress> prog_ref(new FDR::Assertions::BFSRefinementProgress);

		//const std::shared_ptr <FDR::Assertions::Progress> prog;

		//std::cout<< prog->plys()<< std::endl;

		//std::cout <<
		 //std::shared_ptr<FDR::Assertions::Progress>& prog =  FDR::Assertions::Assertion::progress() << std::endl;

		 //const std::shared_ptr<FDR::Assertions::Progress> prog =  assertion->progress();

		// std::cout << prog << std::endl;

		

	    	//FDR::Assertions::BFSRefinementProgress* prog = new FDR::Assertions::BFSRefinementProgress();

		//std::cout << prog->plys() << std::endl; 

		//assertion->progress() = prog_ref;


		//std::cout << prog_ref->plys() << std::endl; 

           
            for (const std::shared_ptr<FDR::Assertions::Counterexample>&
                    counterexample : assertion->counterexamples())
            {
                describe_counterexample(session, *counterexample);
            }
        }
        catch (const FDR::InputFileError& error)
        {
            std::cout << "Could not compile: " << error.what() << std::endl;
            return EXIT_FAILURE;
        }
    }

    return EXIT_SUCCESS;
}

int main(int argc, char** argv)
{
    FDR::library_init(&argc, &argv);

    int return_code = main_function(argc, argv);

    FDR::library_exit();

    return return_code;
}
