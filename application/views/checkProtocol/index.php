<div class="content-wrapper">


    <section class="content-header">

        <h1>

            Formal verification results

        </h1>

        <ol class="breadcrumb">

            <li><a href="<?= base_url(); ?>"><i class="fa fa-dashboard"></i> Home </a></li>

            <li class="active">Formal verification results</li>


        </ol>

    </section>


    <section class="content">

        <div class="row">


            <div class="col-md-12">


                <?php

                echo validation_errors();

                $attributes = array('role' => 'form');

                echo form_open(base_url());

                $nrCouterex = count($fdrTraceLevel1);

                ?>


                <div class="box box-primary" id="top-link">


                    <div class="box-header">
                        <h3 class="box-title">File: <?php


                            if (isset($_SESSION['fileName'])) {
                                echo $_SESSION['fileName'];
                            } else {
                                echo $filename;
                            }

                            if (strpos($filename, 'Error') === false) {
                                $ok = 1;

                            } else {
                                $ok = 0;
                            }
                            ?>
                            &nbsp;
                            <small>
                                <?php
                                echo $fdr_version;

                                ?>
                            </small>
                        </h3>


                        <?php

                        if (isset($prop_strings)) {
                            ?>

                            <button type="button" class="btn btn-primary pull-right" data-toggle="modal"
                                    data-target="#modal-reprez" onclick="representProtocol()">
                                Protocol representation
                            </button>


                            <?php

                        }
                        ?>


                    </div>


                    <?php

                    if ($description !== "") {

                        ?>


                        <div class="modal fade" id="modal-reprez">


                            <div class="modal-dialog">

                                <div class="modal-content">

                                    <div class="modal-header">

                                        <h3 style="color: #1d5da8" class="modal-title">


                                            <?php

                                            if (strcmp($_SESSION['fileName'], "file.spl") !== 0) {
                                                echo $_SESSION['fileName'] . " - ";
                                            }
                                            ?>


                                            Protocol representation</h3>


                                    </div>


                                    <div class="modal-body">

                                        <canvas id="protocol-desc" title="Right click to save the image"
                                                style="border:0px solid;background-color:white">Your web browser does
                                            not supports HTML5!
                                        </canvas>

                                    </div>


                                    <div class="modal-footer ">
                                        <button type="button" class="btn btn-primary pull-right" data-dismiss="modal"
                                                aria-label="Close">
                                            &nbsp;&nbsp; Close &nbsp;&nbsp;&nbsp;
                                        </button>

                                    </div>


                                </div>
                            </div>
                        </div>


                        <?php

                    }
                    ?>


                    <div class="box-body ">

                        <?php

                        if ($ok === 1) {

                            ?>


                            <table class="table table-bordered table-striped wrap_cont">

                                <thead>

                                <tr style="background:#ecf0f5;">

                                    <th>Assertion string</th>

                                    <th>Result</th>


                                </tr>

                                </thead>

                                <tbody>


                                <?php

                                $nrCEX = 0;

                                foreach ($strings as $k => $string) {


                                    ?>

                                    <tr>


                                        <td>
                                            <b>
                                                <!--                                                --><?//= $string['ass_string']; ?>
                                                <!--                                                <br>-->
                                                <?= $prop_strings[$k]["string"]; ?>

                                            </b>
                                            <br>
                                            Visited states:

                                            <span id="visStates<?= $k; ?>"></span>
                                            <br>

                                            <?php
                                            if (strpos($string['result'], '0') === false) {

                                                ?>

                                                <button type="button" class="btn btn-primary pull-right showState"
                                                        data-toggle="modal"
                                                        data-target="#modal-states<?= $nrCEX; ?>">State spaces
                                                </button>

                                                <?php

                                            }
                                            ?>


                                            <div class="modal fade" id="modal-states<?= $nrCEX; ?>">


                                                <div class="modal-dialog">

                                                    <div class="modal-content">

                                                        <div class="modal-header">

                                                            <h3 style="color: #1d5da8" class="modal-title">States:</h3>

                                                        </div>


                                                        <div class="modal-body">

                                                               <span id="state-spaces<?= $nrCEX; ?>">
                                                               </span>


                                                        </div>


                                                        <div class="modal-footer ">
                                                            <button type="button" class="btn btn-primary pull-right"
                                                                    data-dismiss="modal"
                                                                    aria-label="Close">
                                                                &nbsp;&nbsp; Close &nbsp;&nbsp;&nbsp;
                                                            </button>

                                                        </div>


                                                    </div>
                                                </div>
                                            </div>

                                            Visited transitions:

                                            <span id="visTranz<?= $k; ?>"></span>
                                        </td>
                                        <td>
                                            <?php

                                            echo($string['result']);


                                            if (strpos($string['result'], '0') === false) {

                                                ?>

                                                <br>

                                                <?php

                                                echo("Counterexample type: " . $string['counterexample_type']);

                                                echo("<br>" . "Behaviour type: ");
                                                echo(htmlentities($string['behaviour_type']));


                                                ?>


                                                <button class="btn btn-primary pull-right showState"
                                                        id="showCounterexButton<?= $nrCEX; ?>"
                                                        onclick="showCounterex(<?= $nrCEX ?>, '<?= $casperFullTrace[$nrCEX] ?>')">
                                                    Show
                                                </button>

                                                <?php

                                                $nrCEX++;

                                            }
                                            ?>


                                        </td>

                                    </tr>

                                    <?php

                                }
                                ?>


                                </tbody>

                                <tfoot>

                                <tr style="background:#ecf0f5;">

                                    <th>Assertion string</th>

                                    <th>Result</th>

                                </tr>

                                </tfoot>

                            </table>


                            <?php

                        }
                        ?>


                    </div>


                    <div class="box-footer">


                    </div>


                </div>

            </div>


            <div class="col-md-12" id="counterexDiv">


                <div class="box box-primary">


                    <div class="box-header">
                        <h3 class="box-title"> Counterexamples
                            <small></small>
                        </h3>

                    </div>


                    <div class="box-body">

                        <?php

                        $nr = 0;

                        foreach ($casperFullTrace as $k => $trace) {

                            ?>

                            <div class="row" id="showCounterexDiv<?= $k; ?>">

                                <div class="col-md-6">

                                    <div class="box box-body">

                                        <span>

                                        <b>Checking:</b>

                                            <?php

                                            foreach ($prop_strings as $property) {
                                                if ($property['nr'] === $k) {
                                                    echo $property['string'];
                                                }

                                            }

                                            ?>
                                            </span>
                                        <br>
                                        <br>


                                        <b>
                                            Casper (interpret):
                                        </b>

                                        <br>

                                        <b>
                                            Top level trace:
                                        </b>


                                        <?php

                                        echo("<br>" . $casperTraceLevel1[$k] . "<br>");

                                        ?>


                                        <button type="button" class="btn btn-primary pull-right showFdr1"
                                                data-toggle="modal"
                                                data-target="#modal-trace1<?= $k; ?>">Show FDR trace
                                        </button>


                                        <div class="modal fade" id="modal-trace1<?= $k; ?>">


                                            <div class="modal-dialog" style="width: 427px!important;">

                                                <div class="modal-content">

                                                    <div class="modal-header">

                                                        <h3 style="color: #1d5da8" class="modal-title">FDR - Top
                                                            level trace</h3>


                                                    </div>


                                                    <div class="modal-body">
                                                        <p>

                                                            <?php
                                                            echo($fdrTraceLevel1[$k] . "<br>");
                                                            ?>
                                                        </p>

                                                    </div>


                                                    <div class="modal-footer ">
                                                        <button type="button" class="btn btn-primary pull-right"
                                                                data-dismiss="modal"
                                                                aria-label="Close">
                                                            &nbsp;&nbsp; Close &nbsp;&nbsp;&nbsp;
                                                        </button>

                                                    </div>


                                                </div>
                                            </div>
                                        </div>

                                        <br>
                                        <br>


                                        <b>
                                            System level (complete trace):
                                        </b>


                                        <br>

                                        <?php

                                        echo($trace);

                                        ?>


                                        <button type="button" class="btn btn-primary pull-right showFdr2"
                                                data-toggle="modal"
                                                data-target="#modal-trace2<?= $k; ?>">Show FDR trace
                                        </button>


                                        <div class="modal fade" id="modal-trace2<?= $k; ?>">


                                            <div class="modal-dialog" style="width: 500px!important;">

                                                <div class="modal-content">

                                                    <div class="modal-header">

                                                        <h3 style="color: #1d5da8" class="modal-title">FDR - System
                                                            level trace</h3>

                                                    </div>


                                                    <div class="modal-body">
                                                        <p>

                                                            <?php

                                                            foreach ($fdrFullTrace[$k] as $value) {

                                                                echo(htmlentities($value) . "<br>");

                                                            }
                                                            ?>
                                                        </p>

                                                    </div>


                                                    <div class="modal-footer ">
                                                        <button type="button" class="btn btn-primary pull-right"
                                                                data-dismiss="modal"
                                                                aria-label="Close">
                                                            &nbsp;&nbsp; Close &nbsp;&nbsp;&nbsp;
                                                        </button>

                                                    </div>


                                                </div>
                                            </div>
                                        </div>


                                    </div>


                                </div>


                                <div class="col-md-6">


                                    <div id="animation" title="Right click to save the image">

                                        <canvas id="arrows<?= $k; ?>"
                                                style="border:0px solid;background-color:white"
                                        >Your web browser does not supports HTML5!
                                        </canvas>

                                    </div>

                                    <button class="btn btn-primary pull-right" id="topBtn<?= $k; ?>"
                                            style="margin-right: 70px; margin-top: 20px"
                                            onclick="topButton()">Top
                                    </button>


                                </div>


                            </div>

                            <?php

                        }

                        ?>


                    </div>

                </div>


            </div>


        </div>


    </section>

</div>


<script type="text/javascript">


    var actual_JSON;
    var redColor = "#f9040f";
    var blackColor = "#050006";
    // var blueColor = "#537bf9";
    var blueColor = "#1d5da8";

    $('#counterexDiv').hide();


    var k;


    for (k = 0; k <= <?=$nrCouterex?>; k++) {

        //$('#showCounterexButton' + k).hide();

        $("#showCounterexButton" + k).click(function (event) {
            event.preventDefault();
        });

    }


    for (k = 0; k <= <?=$nrCouterex?>; k++) {

        //$('#showCounterexButton' + k).hide();

        $("#topBtn" + k).click(function (event) {
            event.preventDefault();
        });

    }


    for (k = 0; k < <?=$nrCouterex?>; k++) {

        $('#showCounterexDiv' + k).hide();


    }


    function topButton() {

        window.location = "#top-link";
    }


    function drawVerticalArrow(context, xStart, yStart, size, length, color) {


        context.fillStyle = color;

        context.beginPath();

        context.moveTo(xStart - 1, yStart - size);
        context.lineTo(xStart + 1, yStart - size);
        context.lineTo(xStart + 1, yStart - (-length));
        context.lineTo(xStart + 5, yStart - (-length));
        context.lineTo(xStart, yStart - (-length - size));
        context.lineTo(xStart - 5, yStart - (-length));
        context.lineTo(xStart - 1, yStart - (-length));
        context.lineTo(xStart - 1, yStart - size);
        context.fill();

    }

    function drawHorizontalArrowRight(context, xStart, yStart, size, length, color, message, messageColor) {

        context.fillStyle = color;

        context.beginPath();

        context.moveTo(xStart, yStart);
        context.lineTo(xStart, yStart + 2);
        context.lineTo(xStart + length - size, yStart + 2);
        context.lineTo(xStart + length - size, yStart + 2 + 5);
        context.lineTo(xStart + length, yStart + 1);
        context.lineTo(xStart + length - size, yStart - 5);
        context.lineTo(xStart + length - size, yStart);
        context.lineTo(xStart, yStart);
        context.fill();

        if (message !== "") {

            context.beginPath();
            context.fillStyle = messageColor;
            context.font = "bold 12px Arial";

            context.fillText(message, xStart + (length - 29 - (5 * message.length)) / 2, yStart - 6);
        }


    }

    function drawHorizontalArrowLeft(context, xStart, yStart, size, length, color, message, messageColor) {

        context.fillStyle = color;

        context.beginPath();

        context.moveTo(xStart + length, yStart);
        context.lineTo(xStart + length, yStart + 2);
        context.lineTo(xStart + size, yStart + 2);
        context.lineTo(xStart + size, yStart + 2 + 5);
        context.lineTo(xStart, yStart + 1);
        context.lineTo(xStart + size, yStart - 5);
        context.lineTo(xStart + size, yStart);
        context.lineTo(xStart, yStart);
        context.fill();

        if (message !== "") {
            context.beginPath();
            context.fillStyle = messageColor;
            context.font = "bold 12px Arial";
            context.fillText(message, xStart + (length - 25 - (5 * message.length)) / 2, yStart - 6);
        }

    }


    var agents = '<?=$agents?>';
    var free_vars = '<?=$free_vars?>';
    var protocolDescription = '<?=$description?>';

    var bobFlag = true;


    var protocolAgents = agents.split("*");
    var protocolFreeVars = free_vars.split("*");
    protocolDescription = protocolDescription.split("*");


    var ok = true;

    if (protocolAgents.length > 1) {

        var originalIntruderName = protocolAgents[protocolAgents.length - 1].split("=")[1].trim();
        var intruderName = "";

        if ((originalIntruderName.includes("M")) && (originalIntruderName.length === 1)) {

            intruderName = "Mallory";
        }

        if ((originalIntruderName.includes("I")) && (originalIntruderName.length === 1)) {

            intruderName = "Intruder";
        }


        var agentsArray = "";

        var tokens = "";

        for (i = 0; i < protocolAgents.length; i++) {

            if (protocolAgents[i].includes(":")) {

                tokens = protocolAgents[i].split(":");
                if (tokens[1].trim().localeCompare("Agent") === 0) {

                    agentsArray += tokens[0];
                    agentsArray += ",";

                }

                if (tokens[1].trim().localeCompare("Server") === 0) {

                    agentsArray += tokens[0];

                }

                if (tokens[1].trim().localeCompare("Bank") === 0) {

                    agentsArray += tokens[0];
                    bobFlag = false;

                }

            }

        }


        var freeVarsArray = "";
        var auxAgentsArray = "";

        for (i = 0; i < protocolFreeVars.length; i++) {

            if (protocolFreeVars[i].includes(":")) {

                if (agentsArray.length === 0) {


                    tokens = protocolFreeVars[i].split(":");

                    freeVarsArray += tokens[0];
                    freeVarsArray += ",";
                    auxAgentsArray += tokens[1];
                    auxAgentsArray += ",";


                    if (i === 2) {
                        break;
                    }
                }
                else {

                    tokens = protocolFreeVars[i].split(":");
                    if (tokens[1].trim().localeCompare("Agent") === 0) {

                        freeVarsArray += tokens[0];
                        freeVarsArray += ",";

                    }

                    if (tokens[1].trim().localeCompare("Server") === 0) {

                        freeVarsArray += tokens[0];

                    }


                    if (tokens[1].trim().localeCompare("Bank") === 0) {

                        freeVarsArray += tokens[0];
                        bobFlag = false;

                    }

                }
            }
        }


        if (auxAgentsArray.length !== 0) {
            agentsArray = auxAgentsArray;
        }
        // alert(agentsArray);

        var items = freeVarsArray.split(",");

        var freeVars = [];

        for (i = 0; i < items.length; i++) {

            freeVars[i] = items[i].trim();

        }


        items = agentsArray.split(",");

        var agentNames = [];

        for (i = 0; i < items.length; i++) {

            agentNames[i] = items[i].trim();

        }


    }
    else {

        ok = false;
    }


    function representProtocol() {

        if (ok) {

            var canvas = document.getElementById('protocol-desc');

            var context = canvas.getContext('2d');
            context.lineWidth = 1;


            var nrOfVerticalArrows;

            if (freeVars[freeVars.length - 1].length === 0) {

                nrOfVerticalArrows = freeVars.length - 1;
            }
            else {

                nrOfVerticalArrows = freeVars.length;
            }


            var horizoltalArrowLength;

            if (nrOfVerticalArrows === 2) {
                horizoltalArrowLength = 230;
                canvas.width = 310;
                canvas.style.padding = "0px 0px 0px 24%";
            }
            else {
                canvas.style.padding = "0px 0px 0px 0px";
                horizoltalArrowLength = 250;
                canvas.width = 585;

            }


            var nrOfMessages = 0;


            for (i = 0; i < protocolDescription.length; i++) {

                if ((protocolDescription[i].includes(":")) && (protocolDescription[i].includes("->"))) {

                    var aux = protocolDescription[i].split(".")[1].split("->")[1].split(":")[0].trim();

                    if (aux !== "") {

                        nrOfMessages += 1;
                    }
                }

            }


            var verticalArrowLength = (nrOfMessages - 1) * 31;

            canvas.height = verticalArrowLength + 60;

            var xStart = 25;

            var yStart = 40;

            var arrowSize = 8;


            context.beginPath();
            context.font = "23px Arial";
            context.fillStyle = blackColor;


            for (i = 0; i < agentNames.length; i++) {

                if ((agentNames[i].localeCompare(originalIntruderName) !== 0) && (agentNames[i].localeCompare(intruderName) !== 0)) {

                    if (agentNames[i].localeCompare("A") === 0) {

                        context.fillText("Alice", (xStart + 10 - ("Alice".length * 9) / 2), 22);
                        xStart += horizoltalArrowLength;
                        continue;
                    }

                    if (agentNames[i].localeCompare("B") === 0) {

                        if (bobFlag) {

                            context.fillText("Bob", (xStart - ("Bob".length * 9) / 2), 22);

                        }
                        else {
                            context.fillText("Bank", (xStart - ("Bob".length * 9) / 2), 22);
                        }

                        xStart += horizoltalArrowLength;
                        continue;

                    }


                    if (agentNames[i].localeCompare("AuthenticationServer") === 0) {

                        context.fillText(agentNames[i], (xStart - 66 - (agentNames[i].length * 9) / 2), 22);

                    }
                    else {

                        context.fillText(agentNames[i], (xStart - (agentNames[i].length * 9) / 2), 22);
                    }


                    xStart += horizoltalArrowLength;

                }

            }

            xStart = 35;

            for (i = 0; i < nrOfVerticalArrows; i++) {

                drawVerticalArrow(context, xStart, yStart, arrowSize, verticalArrowLength, blackColor);
                xStart += horizoltalArrowLength;
            }

            xStart = 35;
            yStart = 53;


            for (i = 1; i < protocolDescription.length; i++) {

                if ((protocolDescription[i].includes(":")) && (protocolDescription[i].includes("->"))) {

                    var item = protocolDescription[i].split(":");

                    if (item.length === 2) {

                        var agents = item[0].split(".")[1].split("->");

                        if ((agents[0].trim().localeCompare(freeVars[0]) === 0) && (agents[1].trim().localeCompare(freeVars[1]) === 0)) {

                            drawHorizontalArrowRight(context, xStart, yStart, arrowSize, horizoltalArrowLength, blackColor, item[1], blueColor);

                        }

                        if ((agents[0].trim().localeCompare(freeVars[1]) === 0) && (agents[1].trim().localeCompare(freeVars[0]) === 0)) {

                            drawHorizontalArrowLeft(context, xStart, yStart, arrowSize, horizoltalArrowLength, blackColor, item[1], blueColor);

                        }


                        if ((freeVars.length > 2) && (nrOfVerticalArrows === 3)) {

                            if ((agents[0].trim().localeCompare(freeVars[0]) === 0) && (agents[1].trim().localeCompare(freeVars[2]) === 0)) {

                                drawHorizontalArrowRight(context, xStart, yStart, arrowSize, 2 * horizoltalArrowLength, blackColor, item[1], blueColor);

                            }

                            if ((agents[0].trim().localeCompare(freeVars[2]) === 0) && (agents[1].trim().localeCompare(freeVars[0]) === 0)) {

                                drawHorizontalArrowLeft(context, xStart, yStart, arrowSize, 2 * horizoltalArrowLength, blackColor, item[1], blueColor);

                            }

                            if ((agents[0].trim().localeCompare(freeVars[1]) === 0) && (agents[1].trim().localeCompare(freeVars[2]) === 0)) {

                                drawHorizontalArrowRight(context, xStart + horizoltalArrowLength, yStart, arrowSize, horizoltalArrowLength, blackColor, item[1], blueColor);

                            }

                            if ((agents[0].trim().localeCompare(freeVars[2]) === 0) && (agents[1].trim().localeCompare(freeVars[1]) === 0)) {

                                drawHorizontalArrowLeft(context, xStart + horizoltalArrowLength, yStart, arrowSize, horizoltalArrowLength, blackColor, item[1], blueColor);

                            }

                        }

                        yStart += 30;
                    }

                }

            }
        }

        else {
            alert("File must be reloaded from home page! Session expired!")
        }

    }


    function showCounterex(idNr, fullTrace) {

        if (ok) {

            $('#counterexDiv').show();

            $('#showCounterexDiv' + idNr).show();

            window.location = "#showCounterexDiv" + idNr;


            var canvas = document.getElementById('arrows' + idNr);

            var context = canvas.getContext('2d');
            context.lineWidth = 1;


            var items = fullTrace.split('<br>');

            var nrOfVerticalArrows = 0;

            var j;

            var involvedAgents = [];

            var k = 0;


            for (i = 0; i < agentNames.length; i++) {

                for (j = 0; j < items.length; j++) {

                    if (items[j].includes("0.") === false) {

                        if ((items[j].includes("->"))) {

                            var aux = items[j].split(".")[1].split("->")[0].trim();

                            if (aux !== "") {

                                var token = items[j].split(":")[0].split(".")[1].split("->");


                                if ((token[0].trim().localeCompare(agentNames[i]) === 0) || (token[1].trim().localeCompare(agentNames[i]) === 0)) {
                                    nrOfVerticalArrows++;
                                    involvedAgents[k] = agentNames[i];
                                    k++;
                                    break;
                                }
                            }
                        }
                    }
                }
            }


            nrOfVerticalArrows += 1;


            var horizoltalArrowLength;

            canvas.width = 540;

            if (nrOfVerticalArrows === 3) {
                horizoltalArrowLength = 220;
            }
            else {

                if (nrOfVerticalArrows === 2) {
                    horizoltalArrowLength = 220;

                }
                else {
                    horizoltalArrowLength = 151;
                }

            }


            var nrOfMessages = 0;


            for (i = 0; i < items.length; i++) {
                if (items[i].includes("0.") === false) {

                    if (items[i].includes("->")) {

                        var aux = items[i].split(".")[1].split("->")[0].trim();

                        if (aux !== "") {

                            nrOfMessages += 1;
                        }

                    }
                }
            }


            var verticalArrowLength;

            if (nrOfMessages === 1) {
                verticalArrowLength = 50;

            }
            else {

                verticalArrowLength = (nrOfMessages) * 31;
            }


            if (nrOfMessages > 4) {

                canvas.style.padding = "6% 0px 0px 4px";

                if (nrOfVerticalArrows === 4) {
                    canvas.style.padding = "5% 0px 0px 0px";
                }


            }
            else {

                if (nrOfVerticalArrows === 3) {
                    canvas.style.padding = "6% 0px 0px 30px";
                }


                if (nrOfVerticalArrows === 2) {
                    canvas.width = 400;

                    canvas.style.padding = "6% 0px 0px 80px";
                }
                else {
                    canvas.style.padding = "5% 0px 0px 0px";
                }
            }


            canvas.height = verticalArrowLength + 60;

            var xStart = 25;

            var yStart = 40;

            var arrowSize = 8;


            context.fillStyle = redColor;
            context.font = "23px Arial";

            if (intruderName !== "") {
                context.fillText(intruderName, xStart + 16 - (intruderName.length * 9) / 2, 20);
            }
            else {

                context.fillText(originalIntruderName, xStart + 16 - (originalIntruderName.length * 9) / 2, 20);
            }


            context.beginPath();
            context.font = "23px Arial";
            context.fillStyle = blackColor;

            xStart += horizoltalArrowLength;

            for (i = 0; i < involvedAgents.length; i++) {


                if (involvedAgents[i].localeCompare("A") === 0) {

                    context.fillText("Alice", (xStart + 10 - ("Alice".length * 9) / 2), 22);
                    xStart += horizoltalArrowLength;
                    continue;
                }

                if (involvedAgents[i].localeCompare("B") === 0) {

                    context.fillText("Bob", (xStart - ("Bob".length * 9) / 2), 22);
                    xStart += horizoltalArrowLength;
                    continue;

                }


                if (involvedAgents[i].localeCompare("AuthenticationServer") === 0) {

                    context.fillText(involvedAgents[i], (xStart - 66 - (involvedAgents[i].length * 9) / 2), 22);

                }
                else {

                    context.fillText(involvedAgents[i], (xStart - (involvedAgents[i].length * 9) / 2), 22);
                }


                xStart += horizoltalArrowLength;


            }

            xStart = 35;

            drawVerticalArrow(context, xStart, yStart, arrowSize, verticalArrowLength, redColor);


            xStart += horizoltalArrowLength;

            for (i = 1; i < nrOfVerticalArrows; i++) {

                drawVerticalArrow(context, xStart, yStart, arrowSize, verticalArrowLength, blackColor);
                xStart += horizoltalArrowLength;
            }


            xStart = 35;
            yStart = 53;


            for (i = 0; i < items.length; i++) {

                if (items[i].includes("0.") === false) {


                    if (items[i].includes(":")) {

                        var item = items[i].split(":");

                        if (item.length === 2) {

                            var agents = item[0].split(".")[1].split("->");

                            if ((agents[0].trim().localeCompare(involvedAgents[0]) === 0) && (agents[1].trim().localeCompare(involvedAgents[1]) === 0)) {

                                drawHorizontalArrowRight(context, xStart + horizoltalArrowLength, yStart, arrowSize, horizoltalArrowLength, blackColor, item[1], blueColor);

                            }

                            if ((agents[0].trim().localeCompare(involvedAgents[1]) === 0) && (agents[1].trim().localeCompare(involvedAgents[0]) === 0)) {

                                drawHorizontalArrowLeft(context, xStart + horizoltalArrowLength, yStart, arrowSize, horizoltalArrowLength, blackColor, item[1], blueColor);

                            }


                            if (agents[0].trim().includes("I_")) {

                                if (agents[1].trim().localeCompare(involvedAgents[0]) === 0) {

                                    drawHorizontalArrowRight(context, xStart, yStart, arrowSize, horizoltalArrowLength, blackColor, item[1], redColor);
                                }

                                if (agents[1].trim().localeCompare(involvedAgents[1]) === 0) {

                                    drawHorizontalArrowRight(context, xStart, yStart, arrowSize, 2 * horizoltalArrowLength, blackColor, item[1], redColor);
                                }

                            }


                            if (agents[1].trim().includes("I_")) {

                                if (agents[0].trim().localeCompare(involvedAgents[0]) === 0) {

                                    drawHorizontalArrowLeft(context, xStart, yStart, arrowSize, horizoltalArrowLength, blackColor, item[1], blueColor);
                                }

                                if (agents[0].trim().localeCompare(involvedAgents[1]) === 0) {

                                    drawHorizontalArrowLeft(context, xStart, yStart, arrowSize, 2 * horizoltalArrowLength, blackColor, item[1], blueColor);
                                }


                            }


                            if ((involvedAgents.length > 2) && (nrOfVerticalArrows === 4)) {

                                if ((agents[0].trim().localeCompare(involvedAgents[0]) === 0) && (agents[1].trim().localeCompare(involvedAgents[2]) === 0)) {

                                    drawHorizontalArrowRight(context, xStart, yStart, arrowSize, 3 * horizoltalArrowLength, blackColor, item[1], blueColor);

                                }

                                if ((agents[0].trim().localeCompare(involvedAgents[2]) === 0) && (agents[1].trim().localeCompare(involvedAgents[0]) === 0)) {

                                    drawHorizontalArrowLeft(context, xStart, yStart, arrowSize, 3 * horizoltalArrowLength, blackColor, item[1], blueColor);

                                }

                                if ((agents[0].trim().localeCompare(involvedAgents[1]) === 0) && (agents[1].trim().localeCompare(involvedAgents[2]) === 0)) {

                                    drawHorizontalArrowRight(context, xStart + 2 * horizoltalArrowLength, yStart, arrowSize, horizoltalArrowLength, blackColor, item[1], blueColor);

                                }

                                if ((agents[0].trim().localeCompare(involvedAgents[2]) === 0) && (agents[1].trim().localeCompare(involvedAgents[1]) === 0)) {

                                    drawHorizontalArrowLeft(context, xStart + 2 * horizoltalArrowLength, yStart, arrowSize, horizoltalArrowLength, blackColor, item[1], blueColor);

                                }


                                if (agents[0].trim().includes("I_")) {

                                    if (agents[1].trim().localeCompare(involvedAgents[2]) === 0) {

                                        drawHorizontalArrowRight(context, xStart, yStart, arrowSize, 3 * horizoltalArrowLength, blackColor, item[1], redColor);
                                    }

                                }

                                if (agents[1].trim().includes("I_")) {


                                    if (agents[0].trim().localeCompare(involvedAgents[2]) === 0) {

                                        drawHorizontalArrowLeft(context, xStart, yStart, arrowSize, 3 * horizoltalArrowLength, blackColor, item[1], blueColor);
                                    }

                                }

                            }

                            yStart += 30;
                        }

                    }

                }

            }
        }
        else {
            alert("File must be reloaded from home page to see the counterexample! Session expired!")
        }
    }


    loadJSON(function (response) {

        actual_JSON = JSON.parse(response);
        var i;
        var j;
        var nr = 0;

        for (i = 0; i < actual_JSON.results.length; i++) {

            var visitedStates = document.getElementById('visStates' + i);
            visitedStates.innerText = actual_JSON.results[i].visited_states;
            var visitedTranzitons = document.getElementById('visTranz' + i);
            visitedTranzitons.innerText = actual_JSON.results[i].visited_transitions;


            for (j = 0; j < actual_JSON.results[i].counterexamples.length; j++) {

                var states = document.getElementById('state-spaces' + nr);
                states.innerText = actual_JSON.results[i].counterexamples[j].specification_behaviour.states;

            }

            if (actual_JSON.results[i].counterexamples.length !== 0) {

                nr++;
            }
        }

    });


    function loadJSON(callback) {

        var xobj = new XMLHttpRequest();
        xobj.overrideMimeType("application/json");
        xobj.open('POST', 'json_fdr.json', true);
        xobj.onreadystatechange = function () {
            if (xobj.readyState == 4 && xobj.status == 200) {
                callback(xobj.responseText);
            }
        };
        xobj.send(null);
    }


</script>

